import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0036
import IrregularNine14P00C0037
import IrregularNine14P00C0038

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 100 74 153 169 201 137 393), lower := (rows 305 22 100 74 16 32 64 128 256), losses := [] }

theorem u3360 : Upper (D 0) (R 0) [304,20,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3360
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3361 : Route 9 := (fun mask => (mask,id))

def c3361 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3361 : Upper (D 0) (R 0) [304,20,96,129] 13 := by
  apply FastRouting.sound _ _ [304,20,96,129] 13 (by decide) (choices 1) [1,2,8,64,128] r3361 c3361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2194
  · exact u2195
  · exact u2196
  · exact u2197
  · exact u2198

def r3362 : Route 9 := (fun mask => (mask,id))

def c3362 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 256 => 8 | _ => 0)

theorem u3362 : Upper (D 0) (R 0) [304,20,96,130] 13 := by
  apply FastRouting.sound _ _ [304,20,96,130] 13 (by decide) (choices 1) [1,8,64,128] r3362 c3362
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2199
  · exact u2200
  · exact u2201
  · exact u2202

def r3363 : Route 9 := (fun mask => (mask,id))

def c3363 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3363 : Upper (D 0) (R 0) [304,20,96,192] 13 := by
  apply FastRouting.sound _ _ [304,20,96,192] 13 (by decide) (choices 1) [1,2,8,128] r3363 c3363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2203
  · exact u2204
  · exact u2205
  · exact u2206

def r3364 : Route 9 := (fun mask => (mask,id))

def c3364 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3364 : Upper (D 0) (R 0) [304,20,192,65] 13 := by
  apply FastRouting.sound _ _ [304,20,192,65] 13 (by decide) (choices 1) [1,2,8,32,128] r3364 c3364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2207
  · exact u2208
  · exact u2209
  · exact u2210
  · exact u2211

def b3365 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 22 196 74 185 169 233 169 425), lower := (rows 305 22 196 74 16 32 64 128 256), losses := [] }

theorem u3365 : Upper (D 0) (R 0) [304,20,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3365
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3366 : Route 9 := (fun mask => (mask,id))

def c3366 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3366 : Upper (D 0) (R 0) [304,20,192,96] 13 := by
  apply FastRouting.sound _ _ [304,20,192,96] 13 (by decide) (choices 1) [1,2,8,128] r3366 c3366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2212
  · exact u2213
  · exact u2214
  · exact u2215

def b3367 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 305 22 196 200 59 43 107 171 299), lower := (rows 305 22 196 200 16 32 64 128 256), losses := [] }

theorem u3367 : Upper (D 0) (R 0) [304,20,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3367
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 69 74 157 173 205 141 397), lower := (rows 305 50 69 74 16 32 64 128 256), losses := [] }

theorem u3368 : Upper (D 0) (R 0) [304,48,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3368
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 69 137 222 238 206 206 462), lower := (rows 305 50 69 137 16 32 64 128 256), losses := [] }

theorem u3369 : Upper (D 0) (R 0) [304,48,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3369
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 69 138 221 237 205 205 461), lower := (rows 305 50 69 138 16 32 64 128 256), losses := [] }

theorem u3370 : Upper (D 0) (R 0) [304,48,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3370
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 69 140 219 235 203 203 459), lower := (rows 305 50 69 140 16 32 64 128 256), losses := [] }

theorem u3371 : Upper (D 0) (R 0) [304,48,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3371
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 69 200 159 175 207 143 399), lower := (rows 305 50 69 200 16 32 64 128 256), losses := [] }

theorem u3372 : Upper (D 0) (R 0) [304,48,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3372
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 70 140 217 233 201 201 457), lower := (rows 305 50 70 140 16 32 64 128 256), losses := [] }

theorem u3373 : Upper (D 0) (R 0) [304,48,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3373
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 70 200 157 173 205 141 397), lower := (rows 305 50 70 200 16 32 64 128 256), losses := [] }

theorem u3374 : Upper (D 0) (R 0) [304,48,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3374
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 305 50 76 140 211 227 195 195 451), lower := (rows 305 50 76 140 16 32 64 128 256), losses := [] }

theorem u3375 : Upper (D 0) (R 0) [304,48,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3375
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 69 138 188 188 252 188 444), lower := (rows 305 67 69 138 16 32 64 128 256), losses := [] }

theorem u3376 : Upper (D 0) (R 0) [304,65,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3376
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 174, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 69 152 190 174 238 174 430), lower := (rows 305 67 69 152 16 32 64 128 256), losses := [] }

theorem u3377 : Upper (D 0) (R 0) [304,65,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3377
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 70 137 188 188 252 188 444), lower := (rows 305 67 70 137 16 32 64 128 256), losses := [] }

theorem u3378 : Upper (D 0) (R 0) [304,65,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3378
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 70 140 185 185 249 185 441), lower := (rows 305 67 70 140 16 32 64 128 256), losses := [] }

theorem u3379 : Upper (D 0) (R 0) [304,65,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3379
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 173, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 70 152 189 173 237 173 429), lower := (rows 305 67 70 152 16 32 64 128 256), losses := [] }

theorem u3380 : Upper (D 0) (R 0) [304,65,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3380
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3381 : Route 9 := (fun mask => (mask,id))

def c3381 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3381 : Upper (D 0) (R 0) [304,65,72,129] 13 := by
  apply FastRouting.sound _ _ [304,65,72,129] 13 (by decide) (choices 1) [2,4,32,128] r3381 c3381
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2216
  · exact u2217
  · exact u2218
  · exact u2219

def b3382 : PairBound 9 := { available := 181, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 67 76 138 181 181 245 181 437), lower := (rows 305 67 76 138 16 32 64 128 256), losses := [] }

theorem u3382 : Upper (D 0) (R 0) [304,65,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3382
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3383 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 67 76 140 179 179 243 179 435), lower := (rows 305 67 76 140 16 32 64 128 256), losses := [] }

theorem u3383 : Upper (D 0) (R 0) [304,65,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3383
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3384 : Route 9 := (fun mask => (mask,id))

def c3384 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3384 : Upper (D 0) (R 0) [304,65,72,144] 13 := by
  apply FastRouting.sound _ _ [304,65,72,144] 13 (by decide) (choices 1) [1,2,4,32,128] r3384 c3384
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2220
  · exact u2221
  · exact u2222
  · exact u2223
  · exact u2224

def r3385 : Route 9 := (fun mask => (mask,id))

def c3385 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u3385 : Upper (D 0) (R 0) [304,65,80,129] 13 := by
  apply FastRouting.sound _ _ [304,65,80,129] 13 (by decide) (choices 1) [2,4,8,32,128] r3385 c3385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2225
  · exact u2226
  · exact u2227
  · exact u2228
  · exact u2229

def r3386 : Route 9 := (fun mask => (mask,id))

def c3386 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3386 : Upper (D 0) (R 0) [304,65,80,130] 13 := by
  apply FastRouting.sound _ _ [304,65,80,130] 13 (by decide) (choices 1) [1,4,8,32,128] r3386 c3386
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2230
  · exact u2231
  · exact u2232
  · exact u2233
  · exact u2234

def r3387 : Route 9 := (fun mask => (mask,id))

def c3387 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3387 : Upper (D 0) (R 0) [304,65,80,132] 13 := by
  apply FastRouting.sound _ _ [304,65,80,132] 13 (by decide) (choices 1) [1,2,8,32,128] r3387 c3387
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2235
  · exact u2236
  · exact u2237
  · exact u2238
  · exact u2239

def r3388 : Route 9 := (fun mask => (mask,id))

def c3388 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3388 : Upper (D 0) (R 0) [304,65,80,160] 13 := by
  apply FastRouting.sound _ _ [304,65,80,160] 13 (by decide) (choices 1) [1,2,4,8,128] r3388 c3388
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2240
  · exact u2241
  · exact u2242
  · exact u2243
  · exact u2244

theorem m3389_4 : Upper (D 0) (R 0) [304,65,129,192,4] 13 :=
  permutation_upper _ _ _ [304,65,129,192,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2245

def r3389 : Route 9 := (fun mask => (mask,id))

def c3389 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3389 : Upper (D 0) (R 0) [304,65,129,192] 13 := by
  apply FastRouting.sound _ _ [304,65,129,192] 13 (by decide) (choices 1) [2,4,8,32] r3389 c3389
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2245
  · exact m3389_4
  · exact u2246
  · exact u2247

def b3390 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 305 67 134 140 121 121 121 249 377), lower := (rows 305 67 134 140 16 32 64 128 256), losses := [] }

theorem u3390 : Upper (D 0) (R 0) [304,65,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3390
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3391 : Route 9 := (fun mask => (mask,id))

def c3391 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3391 : Upper (D 0) (R 0) [304,65,130,144] 13 := by
  apply FastRouting.sound _ _ [304,65,130,144] 13 (by decide) (choices 1) [1,4,8,32,64] r3391 c3391
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2248
  · exact u2249
  · exact u2250
  · exact u2251
  · exact u2252

def r3392 : Route 9 := (fun mask => (mask,id))

def c3392 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3392 : Upper (D 0) (R 0) [304,65,130,192] 13 := by
  apply FastRouting.sound _ _ [304,65,130,192] 13 (by decide) (choices 1) [1,4,8,32] r3392 c3392
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2253
  · exact u2254
  · exact u2255
  · exact u2256

def b3393 : PairBound 9 := { available := 115, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 140 140 115 115 115 243 371), lower := (rows 305 67 140 140 16 32 64 128 256), losses := [] }

theorem u3393 : Upper (D 0) (R 0) [304,65,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3393
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 103, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 140 152 119 103 103 231 359), lower := (rows 305 67 140 152 16 32 64 128 256), losses := [] }

theorem u3394 : Upper (D 0) (R 0) [304,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3394
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 55, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 140 200 55 55 119 183 311), lower := (rows 305 67 140 200 16 32 64 128 256), losses := [] }

theorem u3395 : Upper (D 0) (R 0) [304,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3395
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3396 : Route 9 := (fun mask => (mask,id))

def c3396 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3396 : Upper (D 0) (R 0) [304,65,144,160] 13 := by
  apply FastRouting.sound _ _ [304,65,144,160] 13 (by decide) (choices 1) [1,2,4,8,64] r3396 c3396
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2257
  · exact u2258
  · exact u2259
  · exact u2260
  · exact u2261

def r3397 : Route 9 := (fun mask => (mask,id))

def c3397 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3397 : Upper (D 0) (R 0) [304,65,144,192] 13 := by
  apply FastRouting.sound _ _ [304,65,144,192] 13 (by decide) (choices 1) [1,2,4,8,32] r3397 c3397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2262
  · exact u2263
  · exact u2264
  · exact u2265
  · exact u2266

def b3398 : PairBound 9 := { available := 169, camps := [{ cop := 6, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 70 152 185 169 233 169 425), lower := (rows 305 70 70 152 16 32 64 128 256), losses := [] }

theorem u3398 : Upper (D 0) (R 0) [304,68,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3398
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3399 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 76 138 177 177 241 177 433), lower := (rows 305 70 76 138 16 32 64 128 256), losses := [] }

theorem u3399 : Upper (D 0) (R 0) [304,68,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3399
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3400 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 76 152 179 163 227 163 419), lower := (rows 305 70 76 152 16 32 64 128 256), losses := [] }

theorem u3400 : Upper (D 0) (R 0) [304,68,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3400
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3401 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 84 138 185 169 233 169 425), lower := (rows 305 70 84 138 16 32 64 128 256), losses := [] }

theorem u3401 : Upper (D 0) (R 0) [304,68,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3401
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3402 : PairBound 9 := { available := 139, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 84 168 155 171 203 139 395), lower := (rows 305 70 84 168 16 32 64 128 256), losses := [] }

theorem u3402 : Upper (D 0) (R 0) [304,68,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3402
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 134 88 185 169 233 169 425), lower := (rows 305 70 134 88 16 32 64 128 256), losses := [] }

theorem u3403 : Upper (D 0) (R 0) [304,68,130,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3403
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 134 200 57 57 121 185 313), lower := (rows 305 70 134 200 16 32 64 128 256), losses := [] }

theorem u3404 : Upper (D 0) (R 0) [304,68,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3404
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 305 70 140 88 179 163 227 163 419), lower := (rows 305 70 140 88 16 32 64 128 256), losses := [] }

theorem u3405 : Upper (D 0) (R 0) [304,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3405
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 140 200 51 51 115 179 307), lower := (rows 305 70 140 200 16 32 64 128 256), losses := [] }

theorem u3406 : Upper (D 0) (R 0) [304,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3406
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3407 : Route 9 := (fun mask => (mask,id))

def c3407 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3407 : Upper (D 0) (R 0) [304,68,144,96] 13 := by
  apply FastRouting.sound _ _ [304,68,144,96] 13 (by decide) (choices 1) [1,2,8,128] r3407 c3407
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2267
  · exact u2268
  · exact u2269
  · exact u2270

def r3408 : Route 9 := (fun mask => (mask,id))

def c3408 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3408 : Upper (D 0) (R 0) [304,68,144,160] 13 := by
  apply FastRouting.sound _ _ [304,68,144,160] 13 (by decide) (choices 1) [1,2,8,64] r3408 c3408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2271
  · exact u2272
  · exact u2273
  · exact u2274

def r3409 : Route 9 := (fun mask => (mask,id))

def c3409 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3409 : Upper (D 0) (R 0) [304,68,144,192] 13 := by
  apply FastRouting.sound _ _ [304,68,144,192] 13 (by decide) (choices 1) [1,2,8,32] r3409 c3409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2275
  · exact u2276
  · exact u2277
  · exact u2278

def b3410 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 2, targets := 1 }], pairs := [(1,0)], upper := (rows 305 70 196 152 59 43 107 171 299), lower := (rows 305 70 196 152 16 32 64 128 256), losses := [] }

theorem u3410 : Upper (D 0) (R 0) [304,68,192,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3410
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r3411 : Route 9 := (fun mask => (mask,id))

def c3411 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3411 : Upper (D 0) (R 0) [304,80,160,192] 13 := by
  apply FastRouting.sound _ _ [304,80,160,192] 13 (by decide) (choices 1) [1,2,4,8] r3411 c3411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2279
  · exact u2280
  · exact u2281
  · exact u2282

def b3412 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 15 19 21 488 496 480 480 480 480), lower := (rows 15 19 21 8 16 32 64 128 256), losses := [] }

theorem u3412 : Upper (D 0) (R 0) [14,17,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3412
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3413 : PairBound 9 := { available := 496, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 37 504 496 496 496 496 496), lower := (rows 15 19 37 8 16 32 64 128 256), losses := [] }

theorem u3413 : Upper (D 0) (R 0) [14,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3413
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3414 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 52 489 497 481 481 481 481), lower := (rows 15 19 52 8 16 32 64 128 256), losses := [] }

theorem u3414 : Upper (D 0) (R 0) [14,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3414
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3415_17 : Upper (D 0) (R 0) [14,17,96,17] 13 :=
  permutation_upper _ _ _ [14,17,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2283

theorem m3415_33 : Upper (D 0) (R 0) [14,17,96,33] 13 :=
  permutation_upper _ _ _ [14,17,33,80] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2285

theorem m3415_48 : Upper (D 0) (R 0) [14,17,96,48] 13 :=
  permutation_upper _ _ _ [14,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2289

theorem m3415_129 : Upper (D 0) (R 0) [14,17,96,129] 13 :=
  permutation_upper _ _ _ [14,17,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2286

theorem m3415_144 : Upper (D 0) (R 0) [14,17,96,144] 13 :=
  permutation_upper _ _ _ [14,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2290

def r3415 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c3415 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3415 : Upper (D 0) (R 0) [14,17,96] 13 := by
  apply FastRouting.sound _ _ [14,17,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160,257,272,288,384] r3415 c3415
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3415_17
  · exact m3415_33
  · exact m3415_48
  · exact u2294
  · exact m3415_129
  · exact m3415_144
  · exact u2295
  · exact u2296
  · exact u2297
  · exact u2298
  · exact u2299

def b3416 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 1 }], pairs := [(3,0)], upper := (rows 15 19 261 248 240 240 240 240 496), lower := (rows 15 19 261 8 16 32 64 128 256), losses := [] }

theorem u3416 : Upper (D 0) (R 0) [14,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3416
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b3417 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 15 19 276 233 241 225 225 225 481), lower := (rows 15 19 276 8 16 32 64 128 256), losses := [] }

theorem u3417 : Upper (D 0) (R 0) [14,17,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3417
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m3418_17 : Upper (D 0) (R 0) [14,17,288,17] 13 :=
  permutation_upper _ _ _ [14,17,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2284

theorem m3418_33 : Upper (D 0) (R 0) [14,17,288,33] 13 :=
  permutation_upper _ _ _ [14,17,33,272] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2287

theorem m3418_48 : Upper (D 0) (R 0) [14,17,288,48] 13 :=
  permutation_upper _ _ _ [14,17,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2292

theorem m3418_65 : Upper (D 0) (R 0) [14,17,288,65] 13 :=
  permutation_upper _ _ _ [14,17,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2288

theorem m3418_80 : Upper (D 0) (R 0) [14,17,288,80] 13 :=
  permutation_upper _ _ _ [14,17,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2293

theorem m3418_96 : Upper (D 0) (R 0) [14,17,288,96] 13 :=
  permutation_upper _ _ _ [14,17,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2298

theorem m3418_192 : Upper (D 0) (R 0) [14,17,288,192] 13 :=
  permutation_upper _ _ _ [14,17,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2299

def r3418 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3418 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3418 : Upper (D 0) (R 0) [14,17,288] 13 := by
  apply FastRouting.sound _ _ [14,17,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3418 c3418
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3418_17
  · exact m3418_33
  · exact m3418_48
  · exact m3418_65
  · exact m3418_80
  · exact m3418_96
  · exact m3418_192

def b3419 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 15 50 52 457 465 481 449 449 449), lower := (rows 15 50 52 8 16 32 64 128 256), losses := [] }

theorem u3419 : Upper (D 0) (R 0) [14,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b3419
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u3419
end Delivery.IrregularNine14.P00
