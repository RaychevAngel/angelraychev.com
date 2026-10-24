import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0218
import IrregularNine14P06C0219
import IrregularNine14P06C0220

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31140 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 69 200 22 305 369 433 305), lower := (rows 11 38 69 200 22 32 64 128 256), losses := [] }

theorem u31140 : Upper (D 6) (R 6) [10,36,65,192,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31140 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31141 : Route 9 := (fun mask => (mask,id))

def c31141 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31141 : Upper (D 6) (R 6) [10,36,65,192,33] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192,33] 13 (by decide) (choices 1) [2,4,16,256] r31141 c31141
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13117
  · exact u13118
  · exact u13119
  · exact u13120

def b31142 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 69 200 50 309 341 405 277), lower := (rows 11 38 69 200 50 32 64 128 256), losses := [] }

theorem u31142 : Upper (D 6) (R 6) [10,36,65,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31142 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31143 : PairBound 9 := { available := 275, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 69 200 52 307 339 403 275), lower := (rows 11 38 69 200 52 32 64 128 256), losses := [] }

theorem u31143 : Upper (D 6) (R 6) [10,36,65,192,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31143 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31144 : Route 9 := (fun mask => (mask,id))

def c31144 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31144 : Upper (D 6) (R 6) [10,36,65,192,257] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192,257] 13 (by decide) (choices 1) [2,4,16] r31144 c31144
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13121
  · exact u13122
  · exact u13123

def r31145 : Route 9 := (fun mask => (mask,id))

def c31145 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31145 : Upper (D 6) (R 6) [10,36,65,192,258] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192,258] 13 (by decide) (choices 1) [1,4,16] r31145 c31145
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13124
  · exact u13125
  · exact u13126

def r31146 : Route 9 := (fun mask => (mask,id))

def c31146 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31146 : Upper (D 6) (R 6) [10,36,65,192,260] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192,260] 13 (by decide) (choices 1) [1,2,16] r31146 c31146
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13127
  · exact u13128
  · exact u13129

def r31147 : Route 9 := (fun mask => (mask,id))

def c31147 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31147 : Upper (D 6) (R 6) [10,36,65,192,288] 13 := by
  apply FastRouting.sound _ _ [10,36,65,192,288] 13 (by decide) (choices 1) [1,2,4,16] r31147 c31147
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13130
  · exact u13131
  · exact u13132
  · exact u13133

def b31148 : PairBound 9 := { available := 116, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 69 392 19 116 116 244 372), lower := (rows 11 38 69 392 19 32 64 128 256), losses := [] }

theorem u31148 : Upper (D 6) (R 6) [10,36,65,384,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31148 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31149 : PairBound 9 := { available := 114, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 69 392 21 114 114 242 370), lower := (rows 11 38 69 392 21 32 64 128 256), losses := [] }

theorem u31149 : Upper (D 6) (R 6) [10,36,65,384,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31149 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31150 : PairBound 9 := { available := 113, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 69 392 22 113 113 241 369), lower := (rows 11 38 69 392 22 32 64 128 256), losses := [] }

theorem u31150 : Upper (D 6) (R 6) [10,36,65,384,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31150 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31151 : Route 9 := (fun mask => (mask,id))

def c31151 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31151 : Upper (D 6) (R 6) [10,36,65,384,33] 13 := by
  apply FastRouting.sound _ _ [10,36,65,384,33] 13 (by decide) (choices 1) [2,4,16,64] r31151 c31151
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13134
  · exact u13135
  · exact u13136
  · exact u13137

def b31152 : PairBound 9 := { available := 85, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 69 392 50 117 85 213 341), lower := (rows 11 38 69 392 50 32 64 128 256), losses := [] }

theorem u31152 : Upper (D 6) (R 6) [10,36,65,384,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31152 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31153 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 69 392 52 115 83 211 339), lower := (rows 11 38 69 392 52 32 64 128 256), losses := [] }

theorem u31153 : Upper (D 6) (R 6) [10,36,65,384,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31153 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31154 : PairBound 9 := { available := 54, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 38 69 392 81 54 118 182 310), lower := (rows 11 38 69 392 81 32 64 128 256), losses := [] }

theorem u31154 : Upper (D 6) (R 6) [10,36,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31154 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31155 : Route 9 := (fun mask => (mask,id))

def c31155 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31155 : Upper (D 6) (R 6) [10,36,65,384,66] 13 := by
  apply FastRouting.sound _ _ [10,36,65,384,66] 13 (by decide) (choices 1) [1,4,16] r31155 c31155
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13138
  · exact u13139
  · exact u13140

def b31156 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 69 392 84 51 115 179 307), lower := (rows 11 38 69 392 84 32 64 128 256), losses := [] }

theorem u31156 : Upper (D 6) (R 6) [10,36,65,384,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31156 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31157 : Route 9 := (fun mask => (mask,id))

def c31157 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31157 : Upper (D 6) (R 6) [10,36,65,384,96] 13 := by
  apply FastRouting.sound _ _ [10,36,65,384,96] 13 (by decide) (choices 1) [1,2,4,16] r31157 c31157
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13141
  · exact u13142
  · exact u13143
  · exact u13144

def b31158 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 38 70 25 21 480 480 480 480), lower := (rows 11 38 70 25 21 32 64 128 256), losses := [] }

theorem u31158 : Upper (D 6) (R 6) [10,36,66,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31158 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31159 : PairBound 9 := { available := 452, camps := [{ cop := 1, region := 25, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 38 70 25 49 484 452 452 452), lower := (rows 11 38 70 25 49 32 64 128 256), losses := [] }

theorem u31159 : Upper (D 6) (R 6) [10,36,66,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31159 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31160 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 25 52 481 449 449 449), lower := (rows 11 38 70 25 52 32 64 128 256), losses := [] }

theorem u31160 : Upper (D 6) (R 6) [10,36,66,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31160 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31161 : PairBound 9 := { available := 420, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 70 25 81 420 484 420 420), lower := (rows 11 38 70 25 81 32 64 128 256), losses := [] }

theorem u31161 : Upper (D 6) (R 6) [10,36,66,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31161 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31162 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 25 84 417 481 417 417), lower := (rows 11 38 70 25 84 32 64 128 256), losses := [] }

theorem u31162 : Upper (D 6) (R 6) [10,36,66,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31162 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31163 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 6, targets := 1 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,0),(2,0),(2,5)], upper := (rows 11 38 70 25 112 421 453 389 389), lower := (rows 11 38 70 25 112 32 64 128 256), losses := [] }

theorem u31163 : Upper (D 6) (R 6) [10,36,66,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31163 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31164 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 38 70 25 145 356 356 484 356), lower := (rows 11 38 70 25 145 32 64 128 256), losses := [] }

theorem u31164 : Upper (D 6) (R 6) [10,36,66,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31164 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31165 : Route 9 := (fun mask => (mask,id))

def c31165 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31165 : Upper (D 6) (R 6) [10,36,66,17,132] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,132] 13 (by decide) (choices 1) [1,64,256] r31165 c31165
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13145
  · exact u13146
  · exact u13147

def r31166 : Route 9 := (fun mask => (mask,id))

def c31166 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31166 : Upper (D 6) (R 6) [10,36,66,17,160] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,160] 13 (by decide) (choices 1) [1,4,64,256] r31166 c31166
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13148
  · exact u13149
  · exact u13150
  · exact u13151

def r31167 : Route 9 := (fun mask => (mask,id))

def c31167 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31167 : Upper (D 6) (R 6) [10,36,66,17,192] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,192] 13 (by decide) (choices 1) [1,4,256] r31167 c31167
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13152
  · exact u13153
  · exact u13154

def r31168 : Route 9 := (fun mask => (mask,id))

def c31168 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31168 : Upper (D 6) (R 6) [10,36,66,17,384] 13 := by
  apply FastRouting.sound _ _ [10,36,66,17,384] 13 (by decide) (choices 1) [1,4,64] r31168 c31168
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13155
  · exact u13156
  · exact u13157

def b31169 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 28 49 481 449 449 449), lower := (rows 11 38 70 28 49 32 64 128 256), losses := [] }

theorem u31169 : Upper (D 6) (R 6) [10,36,66,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31169 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31170 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 28 81 417 481 417 417), lower := (rows 11 38 70 28 81 32 64 128 256), losses := [] }

theorem u31170 : Upper (D 6) (R 6) [10,36,66,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31170 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31171 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 14, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 38 70 28 112 417 449 385 385), lower := (rows 11 38 70 28 112 32 64 128 256), losses := [] }

theorem u31171 : Upper (D 6) (R 6) [10,36,66,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31171 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31172 : Route 9 := (fun mask => (mask,id))

def c31172 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31172 : Upper (D 6) (R 6) [10,36,66,20,129] 13 := by
  apply FastRouting.sound _ _ [10,36,66,20,129] 13 (by decide) (choices 1) [1,64,256] r31172 c31172
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13158
  · exact u13159
  · exact u13160

def b31173 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,5),(4,1),(4,2)], upper := (rows 11 38 70 28 176 353 321 449 321), lower := (rows 11 38 70 28 176 32 64 128 256), losses := [] }

theorem u31173 : Upper (D 6) (R 6) [10,36,66,20,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31173 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31174 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 496, targets := 6 },{ cop := 3, region := 291, targets := 64 }], pairs := [(0,6),(4,1),(4,2)], upper := (rows 11 38 70 28 208 289 353 417 289), lower := (rows 11 38 70 28 208 32 64 128 256), losses := [] }

theorem u31174 : Upper (D 6) (R 6) [10,36,66,20,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31174 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31175 : Route 9 := (fun mask => (mask,id))

def c31175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31175 : Upper (D 6) (R 6) [10,36,66,20,384] 13 := by
  apply FastRouting.sound _ _ [10,36,66,20,384] 13 (by decide) (choices 1) [1,64] r31175 c31175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13161
  · exact u13162

def b31176 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 25, targets := 64 }], pairs := [(0,6),(3,6),(4,6)], upper := (rows 11 38 70 56 21 481 449 449 449), lower := (rows 11 38 70 56 21 32 64 128 256), losses := [] }

theorem u31176 : Upper (D 6) (R 6) [10,36,66,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31176 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31177 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 468, targets := 32 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 11 38 70 56 81 421 453 389 389), lower := (rows 11 38 70 56 81 32 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 10 20 32 64 128 256), good := (rows 11 59 91 56 81 32 64 128 256) }] }

theorem u31177 : Upper (D 6) (R 6) [10,36,66,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31177 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31178 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 56 84 417 449 385 385), lower := (rows 11 38 70 56 84 32 64 128 256), losses := [] }

theorem u31178 : Upper (D 6) (R 6) [10,36,66,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31178 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31179 : Route 9 := (fun mask => (mask,id))

def c31179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31179 : Upper (D 6) (R 6) [10,36,66,48,129] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,129] 13 (by decide) (choices 1) [1,4,64,256] r31179 c31179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13163
  · exact u13164
  · exact u13165
  · exact u13166

def r31180 : Route 9 := (fun mask => (mask,id))

def c31180 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31180 : Upper (D 6) (R 6) [10,36,66,48,132] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,132] 13 (by decide) (choices 1) [1,64,256] r31180 c31180
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13167
  · exact u13168
  · exact u13169

def r31181 : Route 9 := (fun mask => (mask,id))

def c31181 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31181 : Upper (D 6) (R 6) [10,36,66,48,192] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,192] 13 (by decide) (choices 1) [1,4,256] r31181 c31181
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13170
  · exact u13171
  · exact u13172

def r31182 : Route 9 := (fun mask => (mask,id))

def c31182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31182 : Upper (D 6) (R 6) [10,36,66,48,384] 13 := by
  apply FastRouting.sound _ _ [10,36,66,48,384] 13 (by decide) (choices 1) [1,4,64] r31182 c31182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13173
  · exact u13174
  · exact u13175

def b31183 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 25, targets := 32 }], pairs := [(0,5),(3,5),(4,5)], upper := (rows 11 38 70 88 21 417 481 417 417), lower := (rows 11 38 70 88 21 32 64 128 256), losses := [] }

theorem u31183 : Upper (D 6) (R 6) [10,36,66,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31183 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31184 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 452, targets := 32 }], pairs := [(0,2),(2,5),(3,2)], upper := (rows 11 38 70 88 49 421 453 389 389), lower := (rows 11 38 70 88 49 32 64 128 256), losses := [{ target := 2, region := (rows 7 2 0 12 18 32 64 128 256), good := (rows 27 59 91 88 49 32 64 128 256) }] }

theorem u31184 : Upper (D 6) (R 6) [10,36,66,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31184 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31185 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 70 88 52 417 449 385 385), lower := (rows 11 38 70 88 52 32 64 128 256), losses := [] }

theorem u31185 : Upper (D 6) (R 6) [10,36,66,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31185 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31186 : Route 9 := (fun mask => (mask,id))

def c31186 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31186 : Upper (D 6) (R 6) [10,36,66,80,129] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,129] 13 (by decide) (choices 1) [1,4,256] r31186 c31186
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13176
  · exact u13177
  · exact u13178

def r31187 : Route 9 := (fun mask => (mask,id))

def c31187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31187 : Upper (D 6) (R 6) [10,36,66,80,132] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,132] 13 (by decide) (choices 1) [1,256] r31187 c31187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13179
  · exact u13180

def r31188 : Route 9 := (fun mask => (mask,id))

def c31188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31188 : Upper (D 6) (R 6) [10,36,66,80,160] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,160] 13 (by decide) (choices 1) [1,4,256] r31188 c31188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13181
  · exact u13182
  · exact u13183

def r31189 : Route 9 := (fun mask => (mask,id))

def c31189 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31189 : Upper (D 6) (R 6) [10,36,66,80,384] 13 := by
  apply FastRouting.sound _ _ [10,36,66,80,384] 13 (by decide) (choices 1) [1,4] r31189 c31189
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13184
  · exact u13185

def b31190 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 358, targets := 1 },{ cop := 4, region := 488, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 70 137 21 368 368 496 368), lower := (rows 11 38 70 137 21 32 64 128 256), losses := [] }

theorem u31190 : Upper (D 6) (R 6) [10,36,66,129,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31190 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31191 : Route 9 := (fun mask => (mask,id))

def c31191 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31191 : Upper (D 6) (R 6) [10,36,66,129,33] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,33] 13 (by decide) (choices 1) [4,16,64,256] r31191 c31191
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13186
  · exact u13187
  · exact u13188
  · exact u13189

def b31192 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 70 137 52 369 337 465 337), lower := (rows 11 38 70 137 52 32 64 128 256), losses := [] }

theorem u31192 : Upper (D 6) (R 6) [10,36,66,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31192 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31193 : Route 9 := (fun mask => (mask,id))

def c31193 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31193 : Upper (D 6) (R 6) [10,36,66,129,65] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,65] 13 (by decide) (choices 1) [4,16,256] r31193 c31193
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13190
  · exact u13191
  · exact u13192

def b31194 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 70 137 84 305 369 433 305), lower := (rows 11 38 70 137 84 32 64 128 256), losses := [] }

theorem u31194 : Upper (D 6) (R 6) [10,36,66,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31194 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31195 : Route 9 := (fun mask => (mask,id))

def c31195 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31195 : Upper (D 6) (R 6) [10,36,66,129,96] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,96] 13 (by decide) (choices 1) [1,4,16,256] r31195 c31195
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13193
  · exact u13194
  · exact u13195
  · exact u13196

def r31196 : Route 9 := (fun mask => (mask,id))

def c31196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31196 : Upper (D 6) (R 6) [10,36,66,129,257] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,257] 13 (by decide) (choices 1) [4,16,64] r31196 c31196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13197
  · exact u13198
  · exact u13199

def r31197 : Route 9 := (fun mask => (mask,id))

def c31197 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31197 : Upper (D 6) (R 6) [10,36,66,129,260] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,260] 13 (by decide) (choices 1) [1,16,64] r31197 c31197
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13200
  · exact u13201
  · exact u13202

def r31198 : Route 9 := (fun mask => (mask,id))

def c31198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31198 : Upper (D 6) (R 6) [10,36,66,129,288] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,288] 13 (by decide) (choices 1) [1,4,16,64] r31198 c31198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13203
  · exact u13204
  · exact u13205
  · exact u13206

def r31199 : Route 9 := (fun mask => (mask,id))

def c31199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31199 : Upper (D 6) (R 6) [10,36,66,129,320] 13 := by
  apply FastRouting.sound _ _ [10,36,66,129,320] 13 (by decide) (choices 1) [1,4,16] r31199 c31199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13207
  · exact u13208
  · exact u13209

#print axioms u31199
end Delivery.IrregularNine14.P06
