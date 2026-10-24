import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0022

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3420 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 273 120 120 248 376), lower := (rows 35 70 133 137 273 32 64 128 256), losses := [] }

theorem u3420 : Upper (D 3) (R 3) [34,68,129,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3421 : PairBound 9 := { available := 113, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 280 113 113 241 369), lower := (rows 35 70 133 137 280 32 64 128 256), losses := [] }

theorem u3421 : Upper (D 3) (R 3) [34,68,129,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3421
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3422 : PairBound 9 := { available := 89, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 304 121 89 217 345), lower := (rows 35 70 133 137 304 32 64 128 256), losses := [] }

theorem u3422 : Upper (D 3) (R 3) [34,68,129,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3422
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3423 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 336 57 121 185 313), lower := (rows 35 70 133 137 336 32 64 128 256), losses := [] }

theorem u3423 : Upper (D 3) (R 3) [34,68,129,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3423
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3424 : Route 9 := (fun mask => (mask,id))

def c3424 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3424 : Upper (D 3) (R 3) [34,68,129,144,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,257] 13 (by decide) (choices 1) [1,8,64] r3424 c3424
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1320
  · exact u1321
  · exact u1322

def b3425 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 133 152 280 97 97 225 353), lower := (rows 35 70 133 152 280 32 64 128 256), losses := [] }

theorem u3425 : Upper (D 3) (R 3) [34,68,129,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3425
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3426 : Route 9 := (fun mask => (mask,id))

def c3426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3426 : Upper (D 3) (R 3) [34,68,129,144,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,288] 13 (by decide) (choices 1) [1,8,64] r3426 c3426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1323
  · exact u1324
  · exact u1325

def r3427 : Route 9 := (fun mask => (mask,id))

def c3427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3427 : Upper (D 3) (R 3) [34,68,129,144,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144,320] 13 (by decide) (choices 1) [1,8] r3427 c3427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1326
  · exact u1327

def r3428 : Route 9 := (fun mask => (mask,id))

def c3428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3428 : Upper (D 3) (R 3) [34,68,129,160,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,257] 13 (by decide) (choices 1) [1,8,16,64] r3428 c3428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1328
  · exact u1329
  · exact u1330
  · exact u1331

def r3429 : Route 9 := (fun mask => (mask,id))

def c3429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3429 : Upper (D 3) (R 3) [34,68,129,160,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,264] 13 (by decide) (choices 1) [1,16,64] r3429 c3429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1332
  · exact u1333
  · exact u1334

def r3430 : Route 9 := (fun mask => (mask,id))

def c3430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3430 : Upper (D 3) (R 3) [34,68,129,160,320] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160,320] 13 (by decide) (choices 1) [1,8,16] r3430 c3430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1335
  · exact u1336
  · exact u1337

def r3431 : Route 9 := (fun mask => (mask,id))

def c3431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3431 : Upper (D 3) (R 3) [34,68,129,192,257] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,257] 13 (by decide) (choices 1) [1,8,16] r3431 c3431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340

def r3432 : Route 9 := (fun mask => (mask,id))

def c3432 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3432 : Upper (D 3) (R 3) [34,68,129,192,264] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,264] 13 (by decide) (choices 1) [1,16] r3432 c3432
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1341
  · exact u1342

def r3433 : Route 9 := (fun mask => (mask,id))

def c3433 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3433 : Upper (D 3) (R 3) [34,68,129,192,288] 13 := by
  apply FastRouting.sound _ _ [34,68,129,192,288] 13 (by decide) (choices 1) [1,8,16] r3433 c3433
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1343
  · exact u1344
  · exact u1345

def b3434 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 140 25 49 481 449 449 449), lower := (rows 35 70 140 25 49 32 64 128 256), losses := [] }

theorem u3434 : Upper (D 3) (R 3) [34,68,136,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3435 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 140 25 81 417 481 417 417), lower := (rows 35 70 140 25 81 32 64 128 256), losses := [] }

theorem u3435 : Upper (D 3) (R 3) [34,68,136,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3436 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 25 112 417 449 385 385), lower := (rows 35 70 140 25 112 32 64 128 256), losses := [] }

theorem u3436 : Upper (D 3) (R 3) [34,68,136,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3437 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 140 25 145 353 353 481 353), lower := (rows 35 70 140 25 145 32 64 128 256), losses := [] }

theorem u3437 : Upper (D 3) (R 3) [34,68,136,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3437
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3438 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 176 353 321 449 321), lower := (rows 35 70 140 25 176 32 64 128 256), losses := [] }

theorem u3438 : Upper (D 3) (R 3) [34,68,136,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3438
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3439 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 208 289 353 417 289), lower := (rows 35 70 140 25 208 32 64 128 256), losses := [] }

theorem u3439 : Upper (D 3) (R 3) [34,68,136,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3439
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3440 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 140 25 273 225 225 225 481), lower := (rows 35 70 140 25 273 32 64 128 256), losses := [] }

theorem u3440 : Upper (D 3) (R 3) [34,68,136,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3441 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 25 304 225 193 193 449), lower := (rows 35 70 140 25 304 32 64 128 256), losses := [] }

theorem u3441 : Upper (D 3) (R 3) [34,68,136,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3442 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 25 336 161 225 161 417), lower := (rows 35 70 140 25 336 32 64 128 256), losses := [] }

theorem u3442 : Upper (D 3) (R 3) [34,68,136,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3443 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 25 400 97 97 225 353), lower := (rows 35 70 140 25 400 32 64 128 256), losses := [] }

theorem u3443 : Upper (D 3) (R 3) [34,68,136,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3443
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3444 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 265 49 241 209 209 465), lower := (rows 35 70 140 265 49 32 64 128 256), losses := [] }

theorem u3444 : Upper (D 3) (R 3) [34,68,136,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3444
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3445 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 265 81 177 241 177 433), lower := (rows 35 70 140 265 81 32 64 128 256), losses := [] }

theorem u3445 : Upper (D 3) (R 3) [34,68,136,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3446 : Route 9 := (fun mask => (mask,id))

def c3446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3446 : Upper (D 3) (R 3) [34,68,136,257,96] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,96] 13 (by decide) (choices 1) [1,16,128] r3446 c3446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1346
  · exact u1347
  · exact u1348

def b3447 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 360, targets := 128 }], pairs := [(3,7)], upper := (rows 35 70 140 265 145 113 113 241 369), lower := (rows 35 70 140 265 145 32 64 128 256), losses := [] }

theorem u3447 : Upper (D 3) (R 3) [34,68,136,257,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3448 : Route 9 := (fun mask => (mask,id))

def c3448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3448 : Upper (D 3) (R 3) [34,68,136,257,160] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,160] 13 (by decide) (choices 1) [1,16,64] r3448 c3448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1349
  · exact u1350
  · exact u1351

def r3449 : Route 9 := (fun mask => (mask,id))

def c3449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3449 : Upper (D 3) (R 3) [34,68,136,257,192] 13 := by
  apply FastRouting.sound _ _ [34,68,136,257,192] 13 (by decide) (choices 1) [1,16] r3449 c3449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1352
  · exact u1353

def b3450 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 140 280 49 225 193 193 449), lower := (rows 35 70 140 280 49 32 64 128 256), losses := [] }

theorem u3450 : Upper (D 3) (R 3) [34,68,136,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3450
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3451 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 140 280 81 161 225 161 417), lower := (rows 35 70 140 280 81 32 64 128 256), losses := [] }

theorem u3451 : Upper (D 3) (R 3) [34,68,136,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3452 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 140 280 112 161 193 129 385), lower := (rows 35 70 140 280 112 32 64 128 256), losses := [] }

theorem u3452 : Upper (D 3) (R 3) [34,68,136,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3452
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3453 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 145 97 97 225 353), lower := (rows 35 70 140 280 145 32 64 128 256), losses := [] }

theorem u3453 : Upper (D 3) (R 3) [34,68,136,272,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3453
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3454 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 176 97 65 193 321), lower := (rows 35 70 140 280 176 32 64 128 256), losses := [] }

theorem u3454 : Upper (D 3) (R 3) [34,68,136,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3454
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3455 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 140 280 208 33 97 161 289), lower := (rows 35 70 140 280 208 32 64 128 256), losses := [] }

theorem u3455 : Upper (D 3) (R 3) [34,68,136,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3456 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 261 25 25 224 224 224 480), lower := (rows 35 70 261 25 25 32 64 128 256), losses := [] }

theorem u3456 : Upper (D 3) (R 3) [34,68,257,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3457 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 25 49 232 200 200 456), lower := (rows 35 70 261 25 49 32 64 128 256), losses := [] }

theorem u3457 : Upper (D 3) (R 3) [34,68,257,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3458 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 70 261 25 56 225 193 193 449), lower := (rows 35 70 261 25 56 32 64 128 256), losses := [] }

theorem u3458 : Upper (D 3) (R 3) [34,68,257,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3458
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3459 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 261 25 81 168 232 168 424), lower := (rows 35 70 261 25 81 32 64 128 256), losses := [] }

theorem u3459 : Upper (D 3) (R 3) [34,68,257,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3459
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3460 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 25 88 161 225 161 417), lower := (rows 35 70 261 25 88 32 64 128 256), losses := [] }

theorem u3460 : Upper (D 3) (R 3) [34,68,257,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3461 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 25 112 169 201 137 393), lower := (rows 35 70 261 25 112 32 64 128 256), losses := [] }

theorem u3461 : Upper (D 3) (R 3) [34,68,257,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3461
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3462 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 261 25 145 232 232 232 488), lower := (rows 35 70 261 25 145 32 64 128 256), losses := [] }

theorem u3462 : Upper (D 3) (R 3) [34,68,257,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3462
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3463 : Route 9 := (fun mask => (mask,id))

def c3463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3463 : Upper (D 3) (R 3) [34,68,257,17,136] 13 := by
  apply FastRouting.sound _ _ [34,68,257,17,136] 13 (by decide) (choices 1) [1,64,128] r3463 c3463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1354
  · exact u1355
  · exact u1356

def b3464 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 25 176 233 201 201 457), lower := (rows 35 70 261 25 176 32 64 128 256), losses := [] }

theorem u3464 : Upper (D 3) (R 3) [34,68,257,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3464
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3465 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 25 208 169 233 169 425), lower := (rows 35 70 261 25 208 32 64 128 256), losses := [] }

theorem u3465 : Upper (D 3) (R 3) [34,68,257,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3465
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3466 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 41 88 177 209 145 401), lower := (rows 35 70 261 41 88 32 64 128 256), losses := [] }

theorem u3466 : Upper (D 3) (R 3) [34,68,257,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3467 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 41 145 248 216 216 472), lower := (rows 35 70 261 41 145 32 64 128 256), losses := [] }

theorem u3467 : Upper (D 3) (R 3) [34,68,257,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3468 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 41 152 241 209 209 465), lower := (rows 35 70 261 41 152 32 64 128 256), losses := [] }

theorem u3468 : Upper (D 3) (R 3) [34,68,257,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3468
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3469 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 41 208 185 217 153 409), lower := (rows 35 70 261 41 208 32 64 128 256), losses := [] }

theorem u3469 : Upper (D 3) (R 3) [34,68,257,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3469
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3470 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 56 81 169 201 137 393), lower := (rows 35 70 261 56 81 32 64 128 256), losses := [] }

theorem u3470 : Upper (D 3) (R 3) [34,68,257,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3470
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3471 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 56 88 161 193 129 385), lower := (rows 35 70 261 56 88 32 64 128 256), losses := [] }

theorem u3471 : Upper (D 3) (R 3) [34,68,257,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3472 : Route 9 := (fun mask => (mask,id))

def c3472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3472 : Upper (D 3) (R 3) [34,68,257,48,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,129] 13 (by decide) (choices 1) [1,8,64,128] r3472 c3472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1357
  · exact u1358
  · exact u1359
  · exact u1360

def b3473 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 261 56 152 225 193 193 449), lower := (rows 35 70 261 56 152 32 64 128 256), losses := [] }

theorem u3473 : Upper (D 3) (R 3) [34,68,257,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3474 : Route 9 := (fun mask => (mask,id))

def c3474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3474 : Upper (D 3) (R 3) [34,68,257,48,192] 13 := by
  apply FastRouting.sound _ _ [34,68,257,48,192] 13 (by decide) (choices 1) [1,8,128] r3474 c3474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1361
  · exact u1362
  · exact u1363

def b3475 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 145 184 248 184 440), lower := (rows 35 70 261 73 145 32 64 128 256), losses := [] }

theorem u3475 : Upper (D 3) (R 3) [34,68,257,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3476 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 152 177 241 177 433), lower := (rows 35 70 261 73 152 32 64 128 256), losses := [] }

theorem u3476 : Upper (D 3) (R 3) [34,68,257,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3477 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 261 73 176 185 217 153 409), lower := (rows 35 70 261 73 176 32 64 128 256), losses := [] }

theorem u3477 : Upper (D 3) (R 3) [34,68,257,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3477
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3478 : Route 9 := (fun mask => (mask,id))

def c3478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3478 : Upper (D 3) (R 3) [34,68,257,80,129] 13 := by
  apply FastRouting.sound _ _ [34,68,257,80,129] 13 (by decide) (choices 1) [1,8,128] r3478 c3478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1364
  · exact u1365
  · exact u1366

def b3479 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 261 88 152 161 225 161 417), lower := (rows 35 70 261 88 152 32 64 128 256), losses := [] }

theorem u3479 : Upper (D 3) (R 3) [34,68,257,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3479
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3479
end Delivery.IrregularNine14.P03
