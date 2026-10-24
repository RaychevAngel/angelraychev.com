import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0008
import IrregularNine14P03C0009

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2400 : Route 9 := (fun mask => (mask,id))

def c2400 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2400 : Upper (D 3) (R 3) [6,33,72,129,320] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,320] 13 (by decide) (choices 1) [1,16,128] r2400 c2400
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u530
  · exact u531
  · exact u532

def r2401 : Route 9 := (fun mask => (mask,id))

def c2401 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2401 : Upper (D 3) (R 3) [6,33,72,129,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129,384] 13 (by decide) (choices 1) [1,16,64] r2401 c2401
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b2402 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 152 49 481 449 449 449), lower := (rows 7 35 76 152 49 32 64 128 256), losses := [] }

theorem u2402 : Upper (D 3) (R 3) [6,33,72,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2402
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2403 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 81 417 481 417 417), lower := (rows 7 35 76 152 81 32 64 128 256), losses := [] }

theorem u2403 : Upper (D 3) (R 3) [6,33,72,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2403
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2404 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 112 417 449 385 385), lower := (rows 7 35 76 152 112 32 64 128 256), losses := [] }

theorem u2404 : Upper (D 3) (R 3) [6,33,72,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2404
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2405 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 145 353 353 481 353), lower := (rows 7 35 76 152 145 32 64 128 256), losses := [] }

theorem u2405 : Upper (D 3) (R 3) [6,33,72,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2405
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2406 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 176 353 321 449 321), lower := (rows 7 35 76 152 176 32 64 128 256), losses := [] }

theorem u2406 : Upper (D 3) (R 3) [6,33,72,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2406
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2407 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 76 152 208 289 353 417 289), lower := (rows 7 35 76 152 208 32 64 128 256), losses := [] }

theorem u2407 : Upper (D 3) (R 3) [6,33,72,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2407
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2408 : Route 9 := (fun mask => (mask,id))

def c2408 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2408 : Upper (D 3) (R 3) [6,33,72,144,257] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,257] 13 (by decide) (choices 1) [1,64,128] r2408 c2408
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def r2409 : Route 9 := (fun mask => (mask,id))

def c2409 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2409 : Upper (D 3) (R 3) [6,33,72,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144,288] 13 (by decide) (choices 1) [1,64,128] r2409 c2409
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u539
  · exact u540
  · exact u541

def b2410 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 152 336 161 225 161 417), lower := (rows 7 35 76 152 336 32 64 128 256), losses := [] }

theorem u2410 : Upper (D 3) (R 3) [6,33,72,144,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2410
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2411 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 76 152 400 97 97 225 353), lower := (rows 7 35 76 152 400 32 64 128 256), losses := [] }

theorem u2411 : Upper (D 3) (R 3) [6,33,72,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2411
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2412 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 265 49 240 208 208 464), lower := (rows 7 35 76 265 49 32 64 128 256), losses := [] }

theorem u2412 : Upper (D 3) (R 3) [6,33,72,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2412
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2413 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 76 265 81 176 240 176 432), lower := (rows 7 35 76 265 81 32 64 128 256), losses := [] }

theorem u2413 : Upper (D 3) (R 3) [6,33,72,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2413
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2414 : Route 9 := (fun mask => (mask,id))

def c2414 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2414 : Upper (D 3) (R 3) [6,33,72,257,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,96] 13 (by decide) (choices 1) [1,16,128] r2414 c2414
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def r2415 : Route 9 := (fun mask => (mask,id))

def c2415 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2415 : Upper (D 3) (R 3) [6,33,72,257,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,129] 13 (by decide) (choices 1) [16,64,128] r2415 c2415
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u545
  · exact u546
  · exact u547

def r2416 : Route 9 := (fun mask => (mask,id))

def c2416 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2416 : Upper (D 3) (R 3) [6,33,72,257,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,160] 13 (by decide) (choices 1) [1,16,64,128] r2416 c2416
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u548
  · exact u549
  · exact u550
  · exact u551

def r2417 : Route 9 := (fun mask => (mask,id))

def c2417 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2417 : Upper (D 3) (R 3) [6,33,72,257,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,257,192] 13 (by decide) (choices 1) [1,16,128] r2417 c2417
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u552
  · exact u553
  · exact u554

def b2418 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 280 49 225 193 193 449), lower := (rows 7 35 76 280 49 32 64 128 256), losses := [] }

theorem u2418 : Upper (D 3) (R 3) [6,33,72,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2418
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2419 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 81 161 225 161 417), lower := (rows 7 35 76 280 81 32 64 128 256), losses := [] }

theorem u2419 : Upper (D 3) (R 3) [6,33,72,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2419
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2420 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 112 161 193 129 385), lower := (rows 7 35 76 280 112 32 64 128 256), losses := [] }

theorem u2420 : Upper (D 3) (R 3) [6,33,72,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2420
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2421 : Route 9 := (fun mask => (mask,id))

def c2421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2421 : Upper (D 3) (R 3) [6,33,72,272,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,129] 13 (by decide) (choices 1) [1,64,128] r2421 c2421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u555
  · exact u556
  · exact u557

def r2422 : Route 9 := (fun mask => (mask,id))

def c2422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2422 : Upper (D 3) (R 3) [6,33,72,272,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,272,160] 13 (by decide) (choices 1) [1,64,128] r2422 c2422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u558
  · exact u559
  · exact u560

def b2423 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 76 280 208 161 225 161 417), lower := (rows 7 35 76 280 208 32 64 128 256), losses := [] }

theorem u2423 : Upper (D 3) (R 3) [6,33,72,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2423
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2424 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 76 392 49 241 209 209 465), lower := (rows 7 35 76 392 49 32 64 128 256), losses := [] }

theorem u2424 : Upper (D 3) (R 3) [6,33,72,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2424
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2425 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 76 392 81 177 241 177 433), lower := (rows 7 35 76 392 81 32 64 128 256), losses := [] }

theorem u2425 : Upper (D 3) (R 3) [6,33,72,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2425
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2426 : Route 9 := (fun mask => (mask,id))

def c2426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2426 : Upper (D 3) (R 3) [6,33,72,384,96] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,96] 13 (by decide) (choices 1) [1,16,128] r2426 c2426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u561
  · exact u562
  · exact u563

def b2427 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 35 76 392 145 113 113 241 369), lower := (rows 7 35 76 392 145 32 64 128 256), losses := [] }

theorem u2427 : Upper (D 3) (R 3) [6,33,72,384,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2427
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2428 : Route 9 := (fun mask => (mask,id))

def c2428 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2428 : Upper (D 3) (R 3) [6,33,72,384,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,160] 13 (by decide) (choices 1) [1,16,64] r2428 c2428
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u564
  · exact u565
  · exact u566

def r2429 : Route 9 := (fun mask => (mask,id))

def c2429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2429 : Upper (D 3) (R 3) [6,33,72,384,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,192] 13 (by decide) (choices 1) [1,16] r2429 c2429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u567
  · exact u568

def b2430 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 196 25 25 480 480 480 480), lower := (rows 7 35 196 25 25 32 64 128 256), losses := [] }

theorem u2430 : Upper (D 3) (R 3) [6,33,192,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2430
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2431 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 25 49 488 456 456 456), lower := (rows 7 35 196 25 49 32 64 128 256), losses := [] }

theorem u2431 : Upper (D 3) (R 3) [6,33,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2431
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2432 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 25 56 481 449 449 449), lower := (rows 7 35 196 25 56 32 64 128 256), losses := [] }

theorem u2432 : Upper (D 3) (R 3) [6,33,192,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2432
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2433 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 196 25 81 424 488 424 424), lower := (rows 7 35 196 25 81 32 64 128 256), losses := [] }

theorem u2433 : Upper (D 3) (R 3) [6,33,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2433
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2434 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 291, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 25 88 417 481 417 417), lower := (rows 7 35 196 25 88 32 64 128 256), losses := [] }

theorem u2434 : Upper (D 3) (R 3) [6,33,192,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2434
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2435 : PairBound 9 := { available := 393, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 196 25 112 425 457 393 393), lower := (rows 7 35 196 25 112 32 64 128 256), losses := [] }

theorem u2435 : Upper (D 3) (R 3) [6,33,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2435
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2436 : PairBound 9 := { available := 297, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 196 25 208 297 361 425 297), lower := (rows 7 35 196 25 208 32 64 128 256), losses := [] }

theorem u2436 : Upper (D 3) (R 3) [6,33,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2436
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2437 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 196 25 273 232 232 232 488), lower := (rows 7 35 196 25 273 32 64 128 256), losses := [] }

theorem u2437 : Upper (D 3) (R 3) [6,33,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2437
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2438 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2438 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2438 : Upper (D 3) (R 3) [6,33,192,17,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17,264] 13 (by decide) (choices 1) [1,64] r2438 c2438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u569
  · exact u570

def b2439 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 196 25 304 233 201 201 457), lower := (rows 7 35 196 25 304 32 64 128 256), losses := [] }

theorem u2439 : Upper (D 3) (R 3) [6,33,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2439
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2440 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 25 336 169 233 169 425), lower := (rows 7 35 196 25 336 32 64 128 256), losses := [] }

theorem u2440 : Upper (D 3) (R 3) [6,33,192,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2440
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2441 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 88 433 465 401 401), lower := (rows 7 35 196 41 88 32 64 128 256), losses := [] }

theorem u2441 : Upper (D 3) (R 3) [6,33,192,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2441
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2442 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 273 248 216 216 472), lower := (rows 7 35 196 41 273 32 64 128 256), losses := [] }

theorem u2442 : Upper (D 3) (R 3) [6,33,192,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2442
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2443 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 280 241 209 209 465), lower := (rows 7 35 196 41 280 32 64 128 256), losses := [] }

theorem u2443 : Upper (D 3) (R 3) [6,33,192,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2443
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2444 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 196 41 336 185 217 153 409), lower := (rows 7 35 196 41 336 32 64 128 256), losses := [] }

theorem u2444 : Upper (D 3) (R 3) [6,33,192,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2444
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2445 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 56 81 425 457 393 393), lower := (rows 7 35 196 56 81 32 64 128 256), losses := [] }

theorem u2445 : Upper (D 3) (R 3) [6,33,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2445
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2446 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 196 56 88 417 449 385 385), lower := (rows 7 35 196 56 88 32 64 128 256), losses := [] }

theorem u2446 : Upper (D 3) (R 3) [6,33,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2446
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2447 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 196 56 208 297 329 393 265), lower := (rows 7 35 196 56 208 32 64 128 256), losses := [] }

theorem u2447 : Upper (D 3) (R 3) [6,33,192,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2447
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2448 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2448 : Upper (D 3) (R 3) [6,33,192,48,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,257] 13 (by decide) (choices 1) [1,8,64] r2448 c2448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u571
  · exact u572
  · exact u573

def b2449 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 196 56 280 225 193 193 449), lower := (rows 7 35 196 56 280 32 64 128 256), losses := [] }

theorem u2449 : Upper (D 3) (R 3) [6,33,192,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2449
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2450 : Route 9 := (fun mask => (mask,id))

def c2450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2450 : Upper (D 3) (R 3) [6,33,192,48,320] 13 := by
  apply FastRouting.sound _ _ [6,33,192,48,320] 13 (by decide) (choices 1) [1,8,128] r2450 c2450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u574
  · exact u575
  · exact u576

def b2451 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 152 305 369 433 305), lower := (rows 7 35 196 73 152 32 64 128 256), losses := [] }

theorem u2451 : Upper (D 3) (R 3) [6,33,192,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2451
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2452 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 176 313 345 409 281), lower := (rows 7 35 196 73 176 32 64 128 256), losses := [] }

theorem u2452 : Upper (D 3) (R 3) [6,33,192,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2452
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2453 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 273 184 248 184 440), lower := (rows 7 35 196 73 273 32 64 128 256), losses := [] }

theorem u2453 : Upper (D 3) (R 3) [6,33,192,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2453
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2454 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 280 177 241 177 433), lower := (rows 7 35 196 73 280 32 64 128 256), losses := [] }

theorem u2454 : Upper (D 3) (R 3) [6,33,192,65,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2454
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2455 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 304 185 217 153 409), lower := (rows 7 35 196 73 304 32 64 128 256), losses := [] }

theorem u2455 : Upper (D 3) (R 3) [6,33,192,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2455
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2456 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 196 73 400 57 121 185 313), lower := (rows 7 35 196 73 400 32 64 128 256), losses := [] }

theorem u2456 : Upper (D 3) (R 3) [6,33,192,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2456
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2457 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 88 152 289 353 417 289), lower := (rows 7 35 196 88 152 32 64 128 256), losses := [] }

theorem u2457 : Upper (D 3) (R 3) [6,33,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2457
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2458 : Route 9 := (fun mask => (mask,id))

def c2458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2458 : Upper (D 3) (R 3) [6,33,192,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,160] 13 (by decide) (choices 1) [1,8,256] r2458 c2458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u577
  · exact u578
  · exact u579

def r2459 : Route 9 := (fun mask => (mask,id))

def c2459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2459 : Upper (D 3) (R 3) [6,33,192,80,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,257] 13 (by decide) (choices 1) [1,8,128] r2459 c2459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u580
  · exact u581
  · exact u582

#print axioms u2459
end Delivery.IrregularNine14.P03
