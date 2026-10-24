import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0021

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3360 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 28 137 145 353 353 481 353), lower := (rows 35 70 28 137 145 32 64 128 256), losses := [] }

theorem u3360 : Upper (D 3) (R 3) [34,68,24,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3360
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3361 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 137 176 353 321 449 321), lower := (rows 35 70 28 137 176 32 64 128 256), losses := [] }

theorem u3361 : Upper (D 3) (R 3) [34,68,24,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3361
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3362 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 208 289 353 417 289), lower := (rows 35 70 28 137 208 32 64 128 256), losses := [] }

theorem u3362 : Upper (D 3) (R 3) [34,68,24,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3362
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3363 : Route 9 := (fun mask => (mask,id))

def c3363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3363 : Upper (D 3) (R 3) [34,68,24,129,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129,257] 13 (by decide) (choices 1) [1,64,128] r3363 c3363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1274
  · exact u1275
  · exact u1276

def b3364 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 28 137 304 225 193 193 449), lower := (rows 35 70 28 137 304 32 64 128 256), losses := [] }

theorem u3364 : Upper (D 3) (R 3) [34,68,24,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3365 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 137 336 161 225 161 417), lower := (rows 35 70 28 137 336 32 64 128 256), losses := [] }

theorem u3365 : Upper (D 3) (R 3) [34,68,24,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3366 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 137 400 97 97 225 353), lower := (rows 35 70 28 137 400 32 64 128 256), losses := [] }

theorem u3366 : Upper (D 3) (R 3) [34,68,24,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3366
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3367 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 28 168 273 225 193 193 449), lower := (rows 35 70 28 168 273 32 64 128 256), losses := [] }

theorem u3367 : Upper (D 3) (R 3) [34,68,24,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3368 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 28 168 400 97 65 193 321), lower := (rows 35 70 28 168 400 32 64 128 256), losses := [] }

theorem u3368 : Upper (D 3) (R 3) [34,68,24,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3369 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 273 161 225 161 417), lower := (rows 35 70 28 200 273 32 64 128 256), losses := [] }

theorem u3369 : Upper (D 3) (R 3) [34,68,24,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3369
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3370 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 400 33 97 161 289), lower := (rows 35 70 28 200 400 32 64 128 256), losses := [] }

theorem u3370 : Upper (D 3) (R 3) [34,68,24,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3370
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3371 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 25 480 480 480 480), lower := (rows 35 70 133 25 25 32 64 128 256), losses := [] }

theorem u3371 : Upper (D 3) (R 3) [34,68,129,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3372 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 25 49 488 456 456 456), lower := (rows 35 70 133 25 49 32 64 128 256), losses := [] }

theorem u3372 : Upper (D 3) (R 3) [34,68,129,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3373 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 133 25 56 481 449 449 449), lower := (rows 35 70 133 25 56 32 64 128 256), losses := [] }

theorem u3373 : Upper (D 3) (R 3) [34,68,129,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3373
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3374 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 81 424 488 424 424), lower := (rows 35 70 133 25 81 32 64 128 256), losses := [] }

theorem u3374 : Upper (D 3) (R 3) [34,68,129,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3374
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3375 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 25 88 417 481 417 417), lower := (rows 35 70 133 25 88 32 64 128 256), losses := [] }

theorem u3375 : Upper (D 3) (R 3) [34,68,129,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3375
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3376 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 25 112 425 457 393 393), lower := (rows 35 70 133 25 112 32 64 128 256), losses := [] }

theorem u3376 : Upper (D 3) (R 3) [34,68,129,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3376
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3377 : PairBound 9 := { available := 360, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 145 360 360 488 360), lower := (rows 35 70 133 25 145 32 64 128 256), losses := [] }

theorem u3377 : Upper (D 3) (R 3) [34,68,129,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3377
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3378 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 152 353 353 481 353), lower := (rows 35 70 133 25 152 32 64 128 256), losses := [] }

theorem u3378 : Upper (D 3) (R 3) [34,68,129,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3378
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3379 : PairBound 9 := { available := 329, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 25 176 361 329 457 329), lower := (rows 35 70 133 25 176 32 64 128 256), losses := [] }

theorem u3379 : Upper (D 3) (R 3) [34,68,129,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3379
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3380 : PairBound 9 := { available := 297, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 25 208 297 361 425 297), lower := (rows 35 70 133 25 208 32 64 128 256), losses := [] }

theorem u3380 : Upper (D 3) (R 3) [34,68,129,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3380
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3381 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 25 273 232 232 232 488), lower := (rows 35 70 133 25 273 32 64 128 256), losses := [] }

theorem u3381 : Upper (D 3) (R 3) [34,68,129,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3381
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3382 : Route 9 := (fun mask => (mask,id))

def c3382 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3382 : Upper (D 3) (R 3) [34,68,129,17,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,264] 13 (by decide) (choices 1) [1,64,128] r3382 c3382
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1277
  · exact u1278
  · exact u1279

def b3383 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 25 304 233 201 201 457), lower := (rows 35 70 133 25 304 32 64 128 256), losses := [] }

theorem u3383 : Upper (D 3) (R 3) [34,68,129,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3383
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3384 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 25 336 169 233 169 425), lower := (rows 35 70 133 25 336 32 64 128 256), losses := [] }

theorem u3384 : Upper (D 3) (R 3) [34,68,129,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3384
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3385 : Route 9 := (fun mask => (mask,id))

def c3385 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3385 : Upper (D 3) (R 3) [34,68,129,17,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17,384] 13 (by decide) (choices 1) [1,8,64] r3385 c3385
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1280
  · exact u1281
  · exact u1282

def b3386 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 88 433 465 401 401), lower := (rows 35 70 133 41 88 32 64 128 256), losses := [] }

theorem u3386 : Upper (D 3) (R 3) [34,68,129,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3386
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3387 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 152 369 337 465 337), lower := (rows 35 70 133 41 152 32 64 128 256), losses := [] }

theorem u3387 : Upper (D 3) (R 3) [34,68,129,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3387
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3388 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 208 313 345 409 281), lower := (rows 35 70 133 41 208 32 64 128 256), losses := [] }

theorem u3388 : Upper (D 3) (R 3) [34,68,129,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3388
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3389 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 273 248 216 216 472), lower := (rows 35 70 133 41 273 32 64 128 256), losses := [] }

theorem u3389 : Upper (D 3) (R 3) [34,68,129,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3389
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3390 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 280 241 209 209 465), lower := (rows 35 70 133 41 280 32 64 128 256), losses := [] }

theorem u3390 : Upper (D 3) (R 3) [34,68,129,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3390
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3391 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 336 185 217 153 409), lower := (rows 35 70 133 41 336 32 64 128 256), losses := [] }

theorem u3391 : Upper (D 3) (R 3) [34,68,129,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3391
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3392 : PairBound 9 := { available := 89, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 400 121 89 217 345), lower := (rows 35 70 133 41 400 32 64 128 256), losses := [] }

theorem u3392 : Upper (D 3) (R 3) [34,68,129,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3392
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3393 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 56 81 425 457 393 393), lower := (rows 35 70 133 56 81 32 64 128 256), losses := [] }

theorem u3393 : Upper (D 3) (R 3) [34,68,129,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3393
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3394 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 56 88 417 449 385 385), lower := (rows 35 70 133 56 88 32 64 128 256), losses := [] }

theorem u3394 : Upper (D 3) (R 3) [34,68,129,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3394
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3395 : PairBound 9 := { available := 329, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 56 145 361 329 457 329), lower := (rows 35 70 133 56 145 32 64 128 256), losses := [] }

theorem u3395 : Upper (D 3) (R 3) [34,68,129,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3395
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3396 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 56 152 353 321 449 321), lower := (rows 35 70 133 56 152 32 64 128 256), losses := [] }

theorem u3396 : Upper (D 3) (R 3) [34,68,129,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3396
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3397 : Route 9 := (fun mask => (mask,id))

def c3397 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3397 : Upper (D 3) (R 3) [34,68,129,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,192] 13 (by decide) (choices 1) [1,8,256] r3397 c3397
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1283
  · exact u1284
  · exact u1285

def r3398 : Route 9 := (fun mask => (mask,id))

def c3398 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3398 : Upper (D 3) (R 3) [34,68,129,48,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,257] 13 (by decide) (choices 1) [1,8,64,128] r3398 c3398
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1286
  · exact u1287
  · exact u1288
  · exact u1289

def b3399 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 56 280 225 193 193 449), lower := (rows 35 70 133 56 280 32 64 128 256), losses := [] }

theorem u3399 : Upper (D 3) (R 3) [34,68,129,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3399
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3400 : Route 9 := (fun mask => (mask,id))

def c3400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3400 : Upper (D 3) (R 3) [34,68,129,48,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,320] 13 (by decide) (choices 1) [1,8,128] r3400 c3400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1290
  · exact u1291
  · exact u1292

def r3401 : Route 9 := (fun mask => (mask,id))

def c3401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3401 : Upper (D 3) (R 3) [34,68,129,48,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48,384] 13 (by decide) (choices 1) [1,8,64] r3401 c3401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1293
  · exact u1294
  · exact u1295

def b3402 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 152 305 369 433 305), lower := (rows 35 70 133 73 152 32 64 128 256), losses := [] }

theorem u3402 : Upper (D 3) (R 3) [34,68,129,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3403 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 176 313 345 409 281), lower := (rows 35 70 133 73 176 32 64 128 256), losses := [] }

theorem u3403 : Upper (D 3) (R 3) [34,68,129,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3404 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 273 184 248 184 440), lower := (rows 35 70 133 73 273 32 64 128 256), losses := [] }

theorem u3404 : Upper (D 3) (R 3) [34,68,129,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3404
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3405 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 280 177 241 177 433), lower := (rows 35 70 133 73 280 32 64 128 256), losses := [] }

theorem u3405 : Upper (D 3) (R 3) [34,68,129,65,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3406 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 304 185 217 153 409), lower := (rows 35 70 133 73 304 32 64 128 256), losses := [] }

theorem u3406 : Upper (D 3) (R 3) [34,68,129,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3407 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 400 57 121 185 313), lower := (rows 35 70 133 73 400 32 64 128 256), losses := [] }

theorem u3407 : Upper (D 3) (R 3) [34,68,129,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3408 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 88 145 297 361 425 297), lower := (rows 35 70 133 88 145 32 64 128 256), losses := [] }

theorem u3408 : Upper (D 3) (R 3) [34,68,129,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3408
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3409 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 152 289 353 417 289), lower := (rows 35 70 133 88 152 32 64 128 256), losses := [] }

theorem u3409 : Upper (D 3) (R 3) [34,68,129,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3409
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3410 : Route 9 := (fun mask => (mask,id))

def c3410 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3410 : Upper (D 3) (R 3) [34,68,129,80,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,160] 13 (by decide) (choices 1) [1,8,256] r3410 c3410
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1296
  · exact u1297
  · exact u1298

def r3411 : Route 9 := (fun mask => (mask,id))

def c3411 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3411 : Upper (D 3) (R 3) [34,68,129,80,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,257] 13 (by decide) (choices 1) [1,8,128] r3411 c3411
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1299
  · exact u1300
  · exact u1301

def b3412 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 133 88 280 161 225 161 417), lower := (rows 35 70 133 88 280 32 64 128 256), losses := [] }

theorem u3412 : Upper (D 3) (R 3) [34,68,129,80,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3413 : Route 9 := (fun mask => (mask,id))

def c3413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3413 : Upper (D 3) (R 3) [34,68,129,80,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,288] 13 (by decide) (choices 1) [1,8,128] r3413 c3413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1302
  · exact u1303
  · exact u1304

def r3414 : Route 9 := (fun mask => (mask,id))

def c3414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3414 : Upper (D 3) (R 3) [34,68,129,80,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80,384] 13 (by decide) (choices 1) [1,8] r3414 c3414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1305
  · exact u1306

def b3415 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 133 104 145 313 345 409 281), lower := (rows 35 70 133 104 145 32 64 128 256), losses := [] }

theorem u3415 : Upper (D 3) (R 3) [34,68,129,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3415
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3416 : Route 9 := (fun mask => (mask,id))

def c3416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u3416 : Upper (D 3) (R 3) [34,68,129,96,136] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,136] 13 (by decide) (choices 1) [1,16,256] r3416 c3416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1307
  · exact u1308
  · exact u1309

def r3417 : Route 9 := (fun mask => (mask,id))

def c3417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3417 : Upper (D 3) (R 3) [34,68,129,96,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,257] 13 (by decide) (choices 1) [1,8,16,128] r3417 c3417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1310
  · exact u1311
  · exact u1312
  · exact u1313

def r3418 : Route 9 := (fun mask => (mask,id))

def c3418 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3418 : Upper (D 3) (R 3) [34,68,129,96,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,264] 13 (by decide) (choices 1) [1,16,128] r3418 c3418
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1314
  · exact u1315
  · exact u1316

def r3419 : Route 9 := (fun mask => (mask,id))

def c3419 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3419 : Upper (D 3) (R 3) [34,68,129,96,384] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96,384] 13 (by decide) (choices 1) [1,8,16] r3419 c3419
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1317
  · exact u1318
  · exact u1319

#print axioms u3419
end Delivery.IrregularNine14.P03
