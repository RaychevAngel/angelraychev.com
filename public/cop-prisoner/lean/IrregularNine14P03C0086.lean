import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0033
import IrregularNine14P03C0034

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r5160 : Route 9 := (fun mask => (mask,id))

def c5160 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5160 : Upper (D 3) (R 3) [258,36,65,17,136] 13 := by
  apply FastRouting.sound _ _ [258,36,65,17,136] 13 (by decide) (choices 1) [1,64,128] r5160 c5160
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2022
  · exact u2023
  · exact u2024

def b5161 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 25 176 233 201 201 457), lower := (rows 259 38 69 25 176 32 64 128 256), losses := [] }

theorem u5161 : Upper (D 3) (R 3) [258,36,65,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5161
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5162 : Route 9 := (fun mask => (mask,id))

def c5162 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5162 : Upper (D 3) (R 3) [258,36,65,17,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,17,192] 13 (by decide) (choices 1) [1,8,128] r5162 c5162
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2025
  · exact u2026
  · exact u2027

def b5163 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 41 88 177 209 145 401), lower := (rows 259 38 69 41 88 32 64 128 256), losses := [] }

theorem u5163 : Upper (D 3) (R 3) [258,36,65,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5164 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 41 145 248 216 216 472), lower := (rows 259 38 69 41 145 32 64 128 256), losses := [] }

theorem u5164 : Upper (D 3) (R 3) [258,36,65,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5165 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 41 152 241 209 209 465), lower := (rows 259 38 69 41 152 32 64 128 256), losses := [] }

theorem u5165 : Upper (D 3) (R 3) [258,36,65,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5166 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 69 41 208 185 217 153 409), lower := (rows 259 38 69 41 208 32 64 128 256), losses := [] }

theorem u5166 : Upper (D 3) (R 3) [258,36,65,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5167 : PairBound 9 := { available := 137, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 38 69 56 81 169 201 137 393), lower := (rows 259 38 69 56 81 32 64 128 256), losses := [] }

theorem u5167 : Upper (D 3) (R 3) [258,36,65,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5168 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 69 56 88 161 193 129 385), lower := (rows 259 38 69 56 88 32 64 128 256), losses := [] }

theorem u5168 : Upper (D 3) (R 3) [258,36,65,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5168
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5169 : Route 9 := (fun mask => (mask,id))

def c5169 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u5169 : Upper (D 3) (R 3) [258,36,65,48,129] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48,129] 13 (by decide) (choices 1) [1,8,64,128] r5169 c5169
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2028
  · exact u2029
  · exact u2030
  · exact u2031

def b5170 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 69 56 152 225 193 193 449), lower := (rows 259 38 69 56 152 32 64 128 256), losses := [] }

theorem u5170 : Upper (D 3) (R 3) [258,36,65,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5170
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5171 : Route 9 := (fun mask => (mask,id))

def c5171 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5171 : Upper (D 3) (R 3) [258,36,65,48,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,48,192] 13 (by decide) (choices 1) [1,8,128] r5171 c5171
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2032
  · exact u2033
  · exact u2034

def b5172 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 145 184 248 184 440), lower := (rows 259 38 69 73 145 32 64 128 256), losses := [] }

theorem u5172 : Upper (D 3) (R 3) [258,36,65,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5172
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5173 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 152 177 241 177 433), lower := (rows 259 38 69 73 152 32 64 128 256), losses := [] }

theorem u5173 : Upper (D 3) (R 3) [258,36,65,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5174 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 69 73 176 185 217 153 409), lower := (rows 259 38 69 73 176 32 64 128 256), losses := [] }

theorem u5174 : Upper (D 3) (R 3) [258,36,65,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5175 : Route 9 := (fun mask => (mask,id))

def c5175 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5175 : Upper (D 3) (R 3) [258,36,65,80,129] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80,129] 13 (by decide) (choices 1) [1,8,128] r5175 c5175
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2035
  · exact u2036
  · exact u2037

def b5176 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 69 88 152 161 225 161 417), lower := (rows 259 38 69 88 152 32 64 128 256), losses := [] }

theorem u5176 : Upper (D 3) (R 3) [258,36,65,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5177 : Route 9 := (fun mask => (mask,id))

def c5177 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5177 : Upper (D 3) (R 3) [258,36,65,80,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,80,160] 13 (by decide) (choices 1) [1,8,128] r5177 c5177
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2038
  · exact u2039
  · exact u2040

def r5178 : Route 9 := (fun mask => (mask,id))

def c5178 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5178 : Upper (D 3) (R 3) [258,36,65,96,129] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,129] 13 (by decide) (choices 1) [1,8,16,128] r5178 c5178
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2041
  · exact u2042
  · exact u2043
  · exact u2044

def r5179 : Route 9 := (fun mask => (mask,id))

def c5179 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5179 : Upper (D 3) (R 3) [258,36,65,96,136] 13 := by
  apply FastRouting.sound _ _ [258,36,65,96,136] 13 (by decide) (choices 1) [1,16,128] r5179 c5179
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2045
  · exact u2046
  · exact u2047

def b5180 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 38 69 137 145 120 120 248 376), lower := (rows 259 38 69 137 145 32 64 128 256), losses := [] }

theorem u5180 : Upper (D 3) (R 3) [258,36,65,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5181 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 69 137 152 113 113 241 369), lower := (rows 259 38 69 137 152 32 64 128 256), losses := [] }

theorem u5181 : Upper (D 3) (R 3) [258,36,65,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5181
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5182 : Route 9 := (fun mask => (mask,id))

def c5182 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5182 : Upper (D 3) (R 3) [258,36,65,129,160] 13 := by
  apply FastRouting.sound _ _ [258,36,65,129,160] 13 (by decide) (choices 1) [1,8,16,64] r5182 c5182
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2048
  · exact u2049
  · exact u2050
  · exact u2051

def r5183 : Route 9 := (fun mask => (mask,id))

def c5183 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5183 : Upper (D 3) (R 3) [258,36,65,129,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,129,192] 13 (by decide) (choices 1) [1,8,16] r5183 c5183
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2052
  · exact u2053
  · exact u2054

def b5184 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 69 152 152 97 97 225 353), lower := (rows 259 38 69 152 152 32 64 128 256), losses := [] }

theorem u5184 : Upper (D 3) (R 3) [258,36,65,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5184
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5185 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 152 176 105 73 201 329), lower := (rows 259 38 69 152 176 32 64 128 256), losses := [] }

theorem u5185 : Upper (D 3) (R 3) [258,36,65,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5185
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5186 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 69 152 208 41 105 169 297), lower := (rows 259 38 69 152 208 32 64 128 256), losses := [] }

theorem u5186 : Upper (D 3) (R 3) [258,36,65,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5186
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5187 : Route 9 := (fun mask => (mask,id))

def c5187 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5187 : Upper (D 3) (R 3) [258,36,65,160,192] 13 := by
  apply FastRouting.sound _ _ [258,36,65,160,192] 13 (by decide) (choices 1) [1,8,16] r5187 c5187
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2055
  · exact u2056
  · exact u2057

def b5188 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 76 25 49 225 193 193 449), lower := (rows 259 38 76 25 49 32 64 128 256), losses := [] }

theorem u5188 : Upper (D 3) (R 3) [258,36,72,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5188
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5189 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 76 25 81 161 225 161 417), lower := (rows 259 38 76 25 81 32 64 128 256), losses := [] }

theorem u5189 : Upper (D 3) (R 3) [258,36,72,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5189
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5190 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 25 112 161 193 129 385), lower := (rows 259 38 76 25 112 32 64 128 256), losses := [] }

theorem u5190 : Upper (D 3) (R 3) [258,36,72,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5190
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5191 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 76 25 145 225 225 225 481), lower := (rows 259 38 76 25 145 32 64 128 256), losses := [] }

theorem u5191 : Upper (D 3) (R 3) [258,36,72,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5191
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5192 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 76 25 176 225 193 193 449), lower := (rows 259 38 76 25 176 32 64 128 256), losses := [] }

theorem u5192 : Upper (D 3) (R 3) [258,36,72,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5192
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5193 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 25 208 161 225 161 417), lower := (rows 259 38 76 25 208 32 64 128 256), losses := [] }

theorem u5193 : Upper (D 3) (R 3) [258,36,72,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5193
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5194 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 76 137 49 241 209 209 465), lower := (rows 259 38 76 137 49 32 64 128 256), losses := [] }

theorem u5194 : Upper (D 3) (R 3) [258,36,72,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5194
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5195 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 76 137 81 177 241 177 433), lower := (rows 259 38 76 137 81 32 64 128 256), losses := [] }

theorem u5195 : Upper (D 3) (R 3) [258,36,72,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5195
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5196 : Route 9 := (fun mask => (mask,id))

def c5196 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u5196 : Upper (D 3) (R 3) [258,36,72,129,96] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,96] 13 (by decide) (choices 1) [1,16,128] r5196 c5196
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2058
  · exact u2059
  · exact u2060

def b5197 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 259 38 76 137 145 113 113 241 369), lower := (rows 259 38 76 137 145 32 64 128 256), losses := [] }

theorem u5197 : Upper (D 3) (R 3) [258,36,72,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5197
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r5198 : Route 9 := (fun mask => (mask,id))

def c5198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5198 : Upper (D 3) (R 3) [258,36,72,129,160] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,160] 13 (by decide) (choices 1) [1,16,64] r5198 c5198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2061
  · exact u2062
  · exact u2063

def r5199 : Route 9 := (fun mask => (mask,id))

def c5199 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u5199 : Upper (D 3) (R 3) [258,36,72,129,192] 13 := by
  apply FastRouting.sound _ _ [258,36,72,129,192] 13 (by decide) (choices 1) [1,16] r5199 c5199
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u2064
  · exact u2065

def b5200 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 76 152 49 225 193 193 449), lower := (rows 259 38 76 152 49 32 64 128 256), losses := [] }

theorem u5200 : Upper (D 3) (R 3) [258,36,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5200
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5201 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 152 81 161 225 161 417), lower := (rows 259 38 76 152 81 32 64 128 256), losses := [] }

theorem u5201 : Upper (D 3) (R 3) [258,36,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5201
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5202 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 76 152 112 161 193 129 385), lower := (rows 259 38 76 152 112 32 64 128 256), losses := [] }

theorem u5202 : Upper (D 3) (R 3) [258,36,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5202
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5203 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 152 145 97 97 225 353), lower := (rows 259 38 76 152 145 32 64 128 256), losses := [] }

theorem u5203 : Upper (D 3) (R 3) [258,36,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5203
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5204 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 259 38 76 152 176 97 65 193 321), lower := (rows 259 38 76 152 176 32 64 128 256), losses := [] }

theorem u5204 : Upper (D 3) (R 3) [258,36,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5204
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5205 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 38 76 152 208 33 97 161 289), lower := (rows 259 38 76 152 208 32 64 128 256), losses := [] }

theorem u5205 : Upper (D 3) (R 3) [258,36,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5205
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5206 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 196 25 25 225 225 225 481), lower := (rows 259 38 196 25 25 32 64 128 256), losses := [] }

theorem u5206 : Upper (D 3) (R 3) [258,36,192,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5207 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 196 25 49 233 201 201 457), lower := (rows 259 38 196 25 49 32 64 128 256), losses := [] }

theorem u5207 : Upper (D 3) (R 3) [258,36,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5208 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 449, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 196 25 56 225 193 193 449), lower := (rows 259 38 196 25 56 32 64 128 256), losses := [] }

theorem u5208 : Upper (D 3) (R 3) [258,36,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5209 : PairBound 9 := { available := 169, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 38 196 25 81 169 233 169 425), lower := (rows 259 38 196 25 81 32 64 128 256), losses := [] }

theorem u5209 : Upper (D 3) (R 3) [258,36,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5210 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 259 38 196 25 88 161 225 161 417), lower := (rows 259 38 196 25 88 32 64 128 256), losses := [] }

theorem u5210 : Upper (D 3) (R 3) [258,36,192,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5211 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 196 25 112 169 201 137 393), lower := (rows 259 38 196 25 112 32 64 128 256), losses := [] }

theorem u5211 : Upper (D 3) (R 3) [258,36,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5212 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 25 208 41 105 169 297), lower := (rows 259 38 196 25 208 32 64 128 256), losses := [] }

theorem u5212 : Upper (D 3) (R 3) [258,36,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5212
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5213 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 38 196 41 88 177 209 145 401), lower := (rows 259 38 196 41 88 32 64 128 256), losses := [] }

theorem u5213 : Upper (D 3) (R 3) [258,36,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5214 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 259 38 196 56 81 169 201 137 393), lower := (rows 259 38 196 56 81 32 64 128 256), losses := [] }

theorem u5214 : Upper (D 3) (R 3) [258,36,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5215 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 38 196 56 88 161 193 129 385), lower := (rows 259 38 196 56 88 32 64 128 256), losses := [] }

theorem u5215 : Upper (D 3) (R 3) [258,36,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5216 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 259 38 196 56 208 41 73 137 265), lower := (rows 259 38 196 56 208 32 64 128 256), losses := [] }

theorem u5216 : Upper (D 3) (R 3) [258,36,192,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5217 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 152 49 113 177 305), lower := (rows 259 38 196 73 152 32 64 128 256), losses := [] }

theorem u5217 : Upper (D 3) (R 3) [258,36,192,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5217
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5218 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 259 38 196 73 176 57 89 153 281), lower := (rows 259 38 196 73 176 32 64 128 256), losses := [] }

theorem u5218 : Upper (D 3) (R 3) [258,36,192,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b5219 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 259 38 196 88 152 33 97 161 289), lower := (rows 259 38 196 88 152 32 64 128 256), losses := [] }

theorem u5219 : Upper (D 3) (R 3) [258,36,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b5219
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u5219
end Delivery.IrregularNine14.P03
