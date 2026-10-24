import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0033
import IrregularNine14P00C0034

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3180 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 13 13 240 240 240 240 496), lower := (rows 275 98 13 13 16 32 64 128 256), losses := [] }

theorem u3180 : Upper (D 0) (R 0) [274,96,9,5] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3180
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3181 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 25 244 228 228 228 484), lower := (rows 275 98 13 25 16 32 64 128 256), losses := [] }

theorem u3181 : Upper (D 0) (R 0) [274,96,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3181
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3182 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 13 28 241 225 225 225 481), lower := (rows 275 98 13 28 16 32 64 128 256), losses := [] }

theorem u3182 : Upper (D 0) (R 0) [274,96,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3182
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3183 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 13 41 212 244 212 212 468), lower := (rows 275 98 13 41 16 32 64 128 256), losses := [] }

theorem u3183 : Upper (D 0) (R 0) [274,96,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3183
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3184 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 13 44 209 241 209 209 465), lower := (rows 275 98 13 44 16 32 64 128 256), losses := [] }

theorem u3184 : Upper (D 0) (R 0) [274,96,9,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3184
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3185 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 13 56 213 229 197 197 453), lower := (rows 275 98 13 56 16 32 64 128 256), losses := [] }

theorem u3185 : Upper (D 0) (R 0) [274,96,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3185
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3186 : PairBound 9 := { available := 149, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 98 13 104 149 181 213 149 405), lower := (rows 275 98 13 104 16 32 64 128 256), losses := [] }

theorem u3186 : Upper (D 0) (R 0) [274,96,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3186
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3187 : PairBound 9 := { available := 244, camps := [{ cop := 3, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 275 98 13 137 244 244 244 244 500), lower := (rows 275 98 13 137 16 32 64 128 256), losses := [] }

theorem u3187 : Upper (D 0) (R 0) [274,96,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3187
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3188 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3188 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3188 : Upper (D 0) (R 0) [274,96,9,132] 13 := by
  apply FastRouting.sound _ _ [274,96,9,132] 13 (by decide) (choices 1) [1,32,128] r3188 c3188
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2025
  · exact u2026
  · exact u2027

def b3189 : PairBound 9 := { available := 229, camps := [{ cop := 2, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 13 152 245 229 229 229 485), lower := (rows 275 98 13 152 16 32 64 128 256), losses := [] }

theorem u3189 : Upper (D 0) (R 0) [274,96,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3189
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3190 : Route 9 := (fun mask => (mask,id))

def c3190 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3190 : Upper (D 0) (R 0) [274,96,9,160] 13 := by
  apply FastRouting.sound _ _ [274,96,9,160] 13 (by decide) (choices 1) [1,4,64,128] r3190 c3190
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2028
  · exact u2029
  · exact u2030
  · exact u2031

def b3191 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 21 44 217 233 201 201 457), lower := (rows 275 98 21 44 16 32 64 128 256), losses := [] }

theorem u3191 : Upper (D 0) (R 0) [274,96,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3191
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3192 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 21 137 252 236 236 236 492), lower := (rows 275 98 21 137 16 32 64 128 256), losses := [] }

theorem u3192 : Upper (D 0) (R 0) [274,96,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3192
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3193 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 21 140 249 233 233 233 489), lower := (rows 275 98 21 140 16 32 64 128 256), losses := [] }

theorem u3193 : Upper (D 0) (R 0) [274,96,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3193
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3194 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 21 168 221 237 205 205 461), lower := (rows 275 98 21 168 16 32 64 128 256), losses := [] }

theorem u3194 : Upper (D 0) (R 0) [274,96,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3194
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3195 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 275 98 28 41 213 229 197 197 453), lower := (rows 275 98 28 41 16 32 64 128 256), losses := [] }

theorem u3195 : Upper (D 0) (R 0) [274,96,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3195
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3196 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 44 209 225 193 193 449), lower := (rows 275 98 28 44 16 32 64 128 256), losses := [] }

theorem u3196 : Upper (D 0) (R 0) [274,96,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3196
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3197 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 98 28 104 149 165 197 133 389), lower := (rows 275 98 28 104 16 32 64 128 256), losses := [] }

theorem u3197 : Upper (D 0) (R 0) [274,96,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3197
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3198 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3198 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3198 : Upper (D 0) (R 0) [274,96,24,129] 13 := by
  apply FastRouting.sound _ _ [274,96,24,129] 13 (by decide) (choices 1) [1,4,32,128] r3198 c3198
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2032
  · exact u2033
  · exact u2034
  · exact u2035

def b3199 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 226, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 28 140 241 225 225 225 481), lower := (rows 275 98 28 140 16 32 64 128 256), losses := [] }

theorem u3199 : Upper (D 0) (R 0) [274,96,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3199
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3200 : Route 9 := (fun mask => (mask,id))

def c3200 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3200 : Upper (D 0) (R 0) [274,96,24,160] 13 := by
  apply FastRouting.sound _ _ [274,96,24,160] 13 (by decide) (choices 1) [1,4,64,128] r3200 c3200
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2036
  · exact u2037
  · exact u2038
  · exact u2039

def b3201 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 76 153 185 217 153 409), lower := (rows 275 98 37 76 16 32 64 128 256), losses := [] }

theorem u3201 : Upper (D 0) (R 0) [274,96,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3201
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3202 : PairBound 9 := { available := 141, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 88 157 173 205 141 397), lower := (rows 275 98 37 88 16 32 64 128 256), losses := [] }

theorem u3202 : Upper (D 0) (R 0) [274,96,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3202
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3203 : PairBound 9 := { available := 220, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 137 220 252 220 220 476), lower := (rows 275 98 37 137 16 32 64 128 256), losses := [] }

theorem u3203 : Upper (D 0) (R 0) [274,96,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3203
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3204 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 140 217 249 217 217 473), lower := (rows 275 98 37 140 16 32 64 128 256), losses := [] }

theorem u3204 : Upper (D 0) (R 0) [274,96,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3204
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3205 : PairBound 9 := { available := 205, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 152 221 237 205 205 461), lower := (rows 275 98 37 152 16 32 64 128 256), losses := [] }

theorem u3205 : Upper (D 0) (R 0) [274,96,33,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3205
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3206 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 275 98 37 200 157 189 221 157 413), lower := (rows 275 98 37 200 16 32 64 128 256), losses := [] }

theorem u3206 : Upper (D 0) (R 0) [274,96,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3206
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3207 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 44 76 145 177 209 145 401), lower := (rows 275 98 44 76 16 32 64 128 256), losses := [] }

theorem u3207 : Upper (D 0) (R 0) [274,96,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3207
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3208 : Route 9 := (fun mask => (mask,id))

def c3208 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3208 : Upper (D 0) (R 0) [274,96,40,80] 13 := by
  apply FastRouting.sound _ _ [274,96,40,80] 13 (by decide) (choices 1) [1,4,128] r3208 c3208
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2040
  · exact u2041
  · exact u2042

def r3209 : Route 9 := (fun mask => (mask,id))

def c3209 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3209 : Upper (D 0) (R 0) [274,96,40,129] 13 := by
  apply FastRouting.sound _ _ [274,96,40,129] 13 (by decide) (choices 1) [1,4,64,128] r3209 c3209
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2043
  · exact u2044
  · exact u2045
  · exact u2046

def b3210 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 275 98 44 140 209 241 209 209 465), lower := (rows 275 98 44 140 16 32 64 128 256), losses := [] }

theorem u3210 : Upper (D 0) (R 0) [274,96,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3210
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3211 : Route 9 := (fun mask => (mask,id))

def c3211 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3211 : Upper (D 0) (R 0) [274,96,40,144] 13 := by
  apply FastRouting.sound _ _ [274,96,40,144] 13 (by decide) (choices 1) [1,4,64,128] r3211 c3211
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2047
  · exact u2048
  · exact u2049
  · exact u2050

def r3212 : Route 9 := (fun mask => (mask,id))

def c3212 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3212 : Upper (D 0) (R 0) [274,96,40,192] 13 := by
  apply FastRouting.sound _ _ [274,96,40,192] 13 (by decide) (choices 1) [1,4,128] r3212 c3212
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2051
  · exact u2052
  · exact u2053

def r3213 : Route 9 := (fun mask => (mask,id))

def c3213 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3213 : Upper (D 0) (R 0) [274,96,48,129] 13 := by
  apply FastRouting.sound _ _ [274,96,48,129] 13 (by decide) (choices 1) [1,4,8,64,128] r3213 c3213
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2054
  · exact u2055
  · exact u2056
  · exact u2057
  · exact u2058

def r3214 : Route 9 := (fun mask => (mask,id))

def c3214 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3214 : Upper (D 0) (R 0) [274,96,48,132] 13 := by
  apply FastRouting.sound _ _ [274,96,48,132] 13 (by decide) (choices 1) [1,8,64,128] r3214 c3214
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2059
  · exact u2060
  · exact u2061
  · exact u2062

def r3215 : Route 9 := (fun mask => (mask,id))

def c3215 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3215 : Upper (D 0) (R 0) [274,96,48,192] 13 := by
  apply FastRouting.sound _ _ [274,96,48,192] 13 (by decide) (choices 1) [1,4,8,128] r3215 c3215
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2063
  · exact u2064
  · exact u2065
  · exact u2066

def b3216 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 100 137 157 189 221 157 413), lower := (rows 275 98 100 137 16 32 64 128 256), losses := [] }

theorem u3216 : Upper (D 0) (R 0) [274,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3216
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3217 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 100 140 153 185 217 153 409), lower := (rows 275 98 100 140 16 32 64 128 256), losses := [] }

theorem u3217 : Upper (D 0) (R 0) [274,96,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3217
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3218 : PairBound 9 := { available := 141, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 100 152 157 173 205 141 397), lower := (rows 275 98 100 152 16 32 64 128 256), losses := [] }

theorem u3218 : Upper (D 0) (R 0) [274,96,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3218
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3219 : PairBound 9 := { available := 124, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 275 98 133 137 124 124 124 252 380), lower := (rows 275 98 133 137 16 32 64 128 256), losses := [] }

theorem u3219 : Upper (D 0) (R 0) [274,96,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3219
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3220 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 275 98 133 140 121 121 121 249 377), lower := (rows 275 98 133 140 16 32 64 128 256), losses := [] }

theorem u3220 : Upper (D 0) (R 0) [274,96,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3220
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3221 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3221 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3221 : Upper (D 0) (R 0) [274,96,129,144] 13 := by
  apply FastRouting.sound _ _ [274,96,129,144] 13 (by decide) (choices 1) [1,4,8,32] r3221 c3221
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2067
  · exact u2068
  · exact u2069
  · exact u2070

def r3222 : Route 9 := (fun mask => (mask,id))

def c3222 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3222 : Upper (D 0) (R 0) [274,96,129,160] 13 := by
  apply FastRouting.sound _ _ [274,96,129,160] 13 (by decide) (choices 1) [1,4,8,64] r3222 c3222
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2071
  · exact u2072
  · exact u2073
  · exact u2074

def b3223 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 140 140 113 113 113 241 369), lower := (rows 275 98 140 140 16 32 64 128 256), losses := [] }

theorem u3223 : Upper (D 0) (R 0) [274,96,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3223
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3224 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 140 152 117 101 101 229 357), lower := (rows 275 98 140 152 16 32 64 128 256), losses := [] }

theorem u3224 : Upper (D 0) (R 0) [274,96,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3224
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3225 : PairBound 9 := { available := 85, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 140 168 85 117 85 213 341), lower := (rows 275 98 140 168 16 32 64 128 256), losses := [] }

theorem u3225 : Upper (D 0) (R 0) [274,96,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3225
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3226 : Route 9 := (fun mask => (mask,id))

def c3226 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3226 : Upper (D 0) (R 0) [274,96,144,160] 13 := by
  apply FastRouting.sound _ _ [274,96,144,160] 13 (by decide) (choices 1) [1,4,8,64] r3226 c3226
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2075
  · exact u2076
  · exact u2077
  · exact u2078

theorem m3227_8 : Upper (D 0) (R 0) [274,96,160,192,8] 13 :=
  permutation_upper _ _ _ [274,96,160,192,4] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2080

def r3227 : Route 9 := (fun mask => (mask,id))

def c3227 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3227 : Upper (D 0) (R 0) [274,96,160,192] 13 := by
  apply FastRouting.sound _ _ [274,96,160,192] 13 (by decide) (choices 1) [1,4,8] r3227 c3227
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2079
  · exact u2080
  · exact m3227_8

def b3228 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 7 88 248 232 232 232 488), lower := (rows 305 7 7 88 16 32 64 128 256), losses := [] }

theorem u3228 : Upper (D 0) (R 0) [304,5,3,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3228
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3229 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 7 200 248 248 248 248 504), lower := (rows 305 7 7 200 16 32 64 128 256), losses := [] }

theorem u3229 : Upper (D 0) (R 0) [304,5,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3229
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3230 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 13 26 240 224 224 224 480), lower := (rows 305 7 13 26 16 32 64 128 256), losses := [] }

theorem u3230 : Upper (D 0) (R 0) [304,5,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3230
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3231 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 13 74 240 240 240 240 496), lower := (rows 305 7 13 74 16 32 64 128 256), losses := [] }

theorem u3231 : Upper (D 0) (R 0) [304,5,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3231
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3232 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 13 88 242 226 226 226 482), lower := (rows 305 7 13 88 16 32 64 128 256), losses := [] }

theorem u3232 : Upper (D 0) (R 0) [304,5,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3232
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3233 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 13 200 242 242 242 242 498), lower := (rows 305 7 13 200 16 32 64 128 256), losses := [] }

theorem u3233 : Upper (D 0) (R 0) [304,5,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3233
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3234 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 14 25 240 224 224 224 480), lower := (rows 305 7 14 25 16 32 64 128 256), losses := [] }

theorem u3234 : Upper (D 0) (R 0) [304,5,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3234
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3235 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 14 56 209 225 193 193 449), lower := (rows 305 7 14 56 16 32 64 128 256), losses := [] }

theorem u3235 : Upper (D 0) (R 0) [304,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3235
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3236 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 14 73 240 240 240 240 496), lower := (rows 305 7 14 73 16 32 64 128 256), losses := [] }

theorem u3236 : Upper (D 0) (R 0) [304,5,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3236
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3237 : Route 9 := (fun mask => (mask,id))

def c3237 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3237 : Upper (D 0) (R 0) [304,5,10,80] 13 := by
  apply FastRouting.sound _ _ [304,5,10,80] 13 (by decide) (choices 1) [1,32,64,128] r3237 c3237
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2081
  · exact u2082
  · exact u2083
  · exact u2084

def r3238 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3238 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3238 : Upper (D 0) (R 0) [304,5,10,192] 13 := by
  apply FastRouting.sound _ _ [304,5,10,192] 13 (by decide) (choices 1) [1,32,64] r3238 c3238
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u2085
  · exact u2086
  · exact u2087

def b3239 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 21 42 216 232 200 200 456), lower := (rows 305 7 21 42 16 32 64 128 256), losses := [] }

theorem u3239 : Upper (D 0) (R 0) [304,5,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3239
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3239
end Delivery.IrregularNine14.P00
