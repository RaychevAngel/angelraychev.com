import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0034
import IrregularNine14P00C0035

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3240 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 21 74 248 232 232 232 488), lower := (rows 305 7 21 74 16 32 64 128 256), losses := [] }

theorem u3240 : Upper (D 0) (R 0) [304,5,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3240
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3241 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 21 104 218 234 202 202 458), lower := (rows 305 7 21 104 16 32 64 128 256), losses := [] }

theorem u3241 : Upper (D 0) (R 0) [304,5,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3241
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3242 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 21 200 250 234 234 234 490), lower := (rows 305 7 21 200 16 32 64 128 256), losses := [] }

theorem u3242 : Upper (D 0) (R 0) [304,5,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3242
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3243 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 22 73 248 232 232 232 488), lower := (rows 305 7 22 73 16 32 64 128 256), losses := [] }

theorem u3243 : Upper (D 0) (R 0) [304,5,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3243
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3244 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 22 104 217 233 201 201 457), lower := (rows 305 7 22 104 16 32 64 128 256), losses := [] }

theorem u3244 : Upper (D 0) (R 0) [304,5,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3244
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3245 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 22 200 249 233 233 233 489), lower := (rows 305 7 22 200 16 32 64 128 256), losses := [] }

theorem u3245 : Upper (D 0) (R 0) [304,5,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3245
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3246 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 28 42 209 225 193 193 449), lower := (rows 305 7 28 42 16 32 64 128 256), losses := [] }

theorem u3246 : Upper (D 0) (R 0) [304,5,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3246
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3247 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 28 73 242 226 226 226 482), lower := (rows 305 7 28 73 16 32 64 128 256), losses := [] }

theorem u3247 : Upper (D 0) (R 0) [304,5,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3247
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3248 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 28 74 241 225 225 225 481), lower := (rows 305 7 28 74 16 32 64 128 256), losses := [] }

theorem u3248 : Upper (D 0) (R 0) [304,5,24,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3248
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3249 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 28 104 211 227 195 195 451), lower := (rows 305 7 28 104 16 32 64 128 256), losses := [] }

theorem u3249 : Upper (D 0) (R 0) [304,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3249
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3250 : PairBound 9 := { available := 227, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 28 200 243 227 227 227 483), lower := (rows 305 7 28 200 16 32 64 128 256), losses := [] }

theorem u3250 : Upper (D 0) (R 0) [304,5,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3250
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3251 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 52 73 218 234 202 202 458), lower := (rows 305 7 52 73 16 32 64 128 256), losses := [] }

theorem u3251 : Upper (D 0) (R 0) [304,5,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3251
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3252 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 52 74 217 233 201 201 457), lower := (rows 305 7 52 74 16 32 64 128 256), losses := [] }

theorem u3252 : Upper (D 0) (R 0) [304,5,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3252
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3253 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 7 52 200 219 235 203 203 459), lower := (rows 305 7 52 200 16 32 64 128 256), losses := [] }

theorem u3253 : Upper (D 0) (R 0) [304,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3253
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3254 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 26 248 232 232 232 488), lower := (rows 305 7 69 26 16 32 64 128 256), losses := [] }

theorem u3254 : Upper (D 0) (R 0) [304,5,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3254
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3255 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 74 184 184 248 184 440), lower := (rows 305 7 69 74 16 32 64 128 256), losses := [] }

theorem u3255 : Upper (D 0) (R 0) [304,5,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3255
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 88 186 170 234 170 426), lower := (rows 305 7 69 88 16 32 64 128 256), losses := [] }

theorem u3256 : Upper (D 0) (R 0) [304,5,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3256
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 138 248 248 248 248 504), lower := (rows 305 7 69 138 16 32 64 128 256), losses := [] }

theorem u3257 : Upper (D 0) (R 0) [304,5,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3257
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 152 250 234 234 234 490), lower := (rows 305 7 69 152 16 32 64 128 256), losses := [] }

theorem u3258 : Upper (D 0) (R 0) [304,5,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3258
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3259 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 69 200 186 186 250 186 442), lower := (rows 305 7 69 200 16 32 64 128 256), losses := [] }

theorem u3259 : Upper (D 0) (R 0) [304,5,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3259
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3260 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 70 25 248 232 232 232 488), lower := (rows 305 7 70 25 16 32 64 128 256), losses := [] }

theorem u3260 : Upper (D 0) (R 0) [304,5,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3260
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 305 7 70 56 217 233 201 201 457), lower := (rows 305 7 70 56 16 32 64 128 256), losses := [] }

theorem u3261 : Upper (D 0) (R 0) [304,5,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3261
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 70 73 184 184 248 184 440), lower := (rows 305 7 70 73 16 32 64 128 256), losses := [] }

theorem u3262 : Upper (D 0) (R 0) [304,5,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3262
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3263 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 70 88 185 169 233 169 425), lower := (rows 305 7 70 88 16 32 64 128 256), losses := [] }

theorem u3263 : Upper (D 0) (R 0) [304,5,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3263
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3264 : Route 9 := (fun mask => (mask,id))

def c3264 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3264 : Upper (D 0) (R 0) [304,5,66,129] 13 := by
  apply FastRouting.sound _ _ [304,5,66,129] 13 (by decide) (choices 1) [8,32,64,128] r3264 c3264
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2088
  · exact u2089
  · exact u2090
  · exact u2091

def r3265 : Route 9 := (fun mask => (mask,id))

def c3265 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3265 : Upper (D 0) (R 0) [304,5,66,144] 13 := by
  apply FastRouting.sound _ _ [304,5,66,144] 13 (by decide) (choices 1) [1,8,32,64,128] r3265 c3265
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2092
  · exact u2093
  · exact u2094
  · exact u2095
  · exact u2096

def b3266 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 70 200 185 185 249 185 441), lower := (rows 305 7 70 200 16 32 64 128 256), losses := [] }

theorem u3266 : Upper (D 0) (R 0) [304,5,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3266
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 76 25 242 226 226 226 482), lower := (rows 305 7 76 25 16 32 64 128 256), losses := [] }

theorem u3267 : Upper (D 0) (R 0) [304,5,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3267
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 225, camps := [], pairs := [(2,4)], upper := (rows 305 7 76 26 241 225 225 225 481), lower := (rows 305 7 76 26 16 32 64 128 256), losses := [{ target := 4, region := (rows 1 2 12 8 0 35 67 131 259), good := (rows 481 487 76 494 0 32 64 128 256) }] }

theorem u3268 : Upper (D 0) (R 0) [304,5,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3268
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 305 7 76 56 211 227 195 195 451), lower := (rows 305 7 76 56 16 32 64 128 256), losses := [] }

theorem u3269 : Upper (D 0) (R 0) [304,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3269
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 76 73 178 178 242 178 434), lower := (rows 305 7 76 73 16 32 64 128 256), losses := [] }

theorem u3270 : Upper (D 0) (R 0) [304,5,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3270
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 74 177 177 241 177 433), lower := (rows 305 7 76 74 16 32 64 128 256), losses := [] }

theorem u3271 : Upper (D 0) (R 0) [304,5,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3271
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 88 179 163 227 163 419), lower := (rows 305 7 76 88 16 32 64 128 256), losses := [] }

theorem u3272 : Upper (D 0) (R 0) [304,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3272
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3273 : Route 9 := (fun mask => (mask,id))

def c3273 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3273 : Upper (D 0) (R 0) [304,5,72,129] 13 := by
  apply FastRouting.sound _ _ [304,5,72,129] 13 (by decide) (choices 1) [2,32,64,128] r3273 c3273
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2097
  · exact u2098
  · exact u2099
  · exact u2100

def r3274 : Route 9 := (fun mask => (mask,id))

def c3274 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3274 : Upper (D 0) (R 0) [304,5,72,130] 13 := by
  apply FastRouting.sound _ _ [304,5,72,130] 13 (by decide) (choices 1) [1,32,64,128] r3274 c3274
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2101
  · exact u2102
  · exact u2103
  · exact u2104

def r3275 : Route 9 := (fun mask => (mask,id))

def c3275 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3275 : Upper (D 0) (R 0) [304,5,72,144] 13 := by
  apply FastRouting.sound _ _ [304,5,72,144] 13 (by decide) (choices 1) [1,2,32,64,128] r3275 c3275
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2105
  · exact u2106
  · exact u2107
  · exact u2108
  · exact u2109

def b3276 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 200 179 179 243 179 435), lower := (rows 305 7 76 200 16 32 64 128 256), losses := [] }

theorem u3276 : Upper (D 0) (R 0) [304,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3276
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 42 217 233 201 201 457), lower := (rows 305 7 84 42 16 32 64 128 256), losses := [] }

theorem u3277 : Upper (D 0) (R 0) [304,5,80,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3277
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 73 186 170 234 170 426), lower := (rows 305 7 84 73 16 32 64 128 256), losses := [] }

theorem u3278 : Upper (D 0) (R 0) [304,5,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3278
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 74 185 169 233 169 425), lower := (rows 305 7 84 74 16 32 64 128 256), losses := [] }

theorem u3279 : Upper (D 0) (R 0) [304,5,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3279
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 104 155 171 203 139 395), lower := (rows 305 7 84 104 16 32 64 128 256), losses := [] }

theorem u3280 : Upper (D 0) (R 0) [304,5,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3280
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 137 250 234 234 234 490), lower := (rows 305 7 84 137 16 32 64 128 256), losses := [] }

theorem u3281 : Upper (D 0) (R 0) [304,5,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3281
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 233, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 138 249 233 233 233 489), lower := (rows 305 7 84 138 16 32 64 128 256), losses := [] }

theorem u3282 : Upper (D 0) (R 0) [304,5,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3282
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 168 219 235 203 203 459), lower := (rows 305 7 84 168 16 32 64 128 256), losses := [] }

theorem u3283 : Upper (D 0) (R 0) [304,5,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3283
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3284 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 200 187 171 235 171 427), lower := (rows 305 7 84 200 16 32 64 128 256), losses := [] }

theorem u3284 : Upper (D 0) (R 0) [304,5,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3284
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3285 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 305 7 196 25 250 234 234 234 490), lower := (rows 305 7 196 25 16 32 64 128 256), losses := [] }

theorem u3285 : Upper (D 0) (R 0) [304,5,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3285
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3286 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3286 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u3286 : Upper (D 0) (R 0) [304,5,192,18] 13 := by
  apply FastRouting.sound _ _ [304,5,192,18] 13 (by decide) (choices 1) [1,8,32,64] r3286 c3286
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2110
  · exact u2111
  · exact u2112
  · exact u2113

def b3287 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 305 7 196 56 219 235 203 203 459), lower := (rows 305 7 196 56 16 32 64 128 256), losses := [] }

theorem u3287 : Upper (D 0) (R 0) [304,5,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3287
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3288 : Route 9 := (fun mask => (mask,id))

def c3288 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3288 : Upper (D 0) (R 0) [304,5,192,65] 13 := by
  apply FastRouting.sound _ _ [304,5,192,65] 13 (by decide) (choices 1) [2,8,32,128] r3288 c3288
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2114
  · exact u2115
  · exact u2116
  · exact u2117

def b3289 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 7 196 74 185 185 249 185 441), lower := (rows 305 7 196 74 16 32 64 128 256), losses := [] }

theorem u3289 : Upper (D 0) (R 0) [304,5,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3289
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3290 : Route 9 := (fun mask => (mask,id))

def c3290 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3290 : Upper (D 0) (R 0) [304,5,192,80] 13 := by
  apply FastRouting.sound _ _ [304,5,192,80] 13 (by decide) (choices 1) [1,2,8,32,128] r3290 c3290
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2118
  · exact u2119
  · exact u2120
  · exact u2121
  · exact u2122

def b3291 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 305 7 196 200 59 59 123 187 315), lower := (rows 305 7 196 200 16 32 64 128 256), losses := [] }

theorem u3291 : Upper (D 0) (R 0) [304,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3291
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3292 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 21 73 242 226 226 226 482), lower := (rows 305 14 21 73 16 32 64 128 256), losses := [] }

theorem u3292 : Upper (D 0) (R 0) [304,12,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3292
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3293 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 21 74 241 225 225 225 481), lower := (rows 305 14 21 74 16 32 64 128 256), losses := [] }

theorem u3293 : Upper (D 0) (R 0) [304,12,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3293
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 21 104 211 227 195 195 451), lower := (rows 305 14 21 104 16 32 64 128 256), losses := [] }

theorem u3294 : Upper (D 0) (R 0) [304,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3294
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 21 200 243 227 227 227 483), lower := (rows 305 14 21 200 16 32 64 128 256), losses := [] }

theorem u3295 : Upper (D 0) (R 0) [304,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3295
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 14 22 73 241 225 225 225 481), lower := (rows 305 14 22 73 16 32 64 128 256), losses := [] }

theorem u3296 : Upper (D 0) (R 0) [304,12,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3296
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 14 22 104 209 225 193 193 449), lower := (rows 305 14 22 104 16 32 64 128 256), losses := [] }

theorem u3297 : Upper (D 0) (R 0) [304,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3297
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3298 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 305 14 22 200 241 225 225 225 481), lower := (rows 305 14 22 200 16 32 64 128 256), losses := [] }

theorem u3298 : Upper (D 0) (R 0) [304,12,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3298
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3299 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 305 14 52 73 211 227 195 195 451), lower := (rows 305 14 52 73 16 32 64 128 256), losses := [] }

theorem u3299 : Upper (D 0) (R 0) [304,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3299
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3299
end Delivery.IrregularNine14.P00
