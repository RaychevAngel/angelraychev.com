import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0020

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m2460_128 : Upper (D 0) (R 0) [50,12,65,129,128] 13 :=
  permutation_upper _ _ _ [50,12,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1201

def r2460 : Route 9 := (fun mask => (mask,id))

def c2460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u2460 : Upper (D 0) (R 0) [50,12,65,129] 13 := by
  apply FastRouting.sound _ _ [50,12,65,129] 13 (by decide) (choices 1) [32,64,128,256] r2460 c2460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1200
  · exact u1201
  · exact m2460_128
  · exact u1202

def b2461 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 452, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 152 497 481 481 481 481), lower := (rows 51 14 69 152 16 32 64 128 256), losses := [] }

theorem u2461 : Upper (D 0) (R 0) [50,12,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2461
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 69 200 433 433 497 433 433), lower := (rows 51 14 69 200 16 32 64 128 256), losses := [] }

theorem u2462 : Upper (D 0) (R 0) [50,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2462
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2463 : Route 9 := (fun mask => (mask,id))

def c2463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2463 : Upper (D 0) (R 0) [50,12,65,257] 13 := by
  apply FastRouting.sound _ _ [50,12,65,257] 13 (by decide) (choices 1) [32,64,128] r2463 c2463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1203
  · exact u1204
  · exact u1205

def b2464 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 69 280 241 225 225 225 481), lower := (rows 51 14 69 280 16 32 64 128 256), losses := [] }

theorem u2464 : Upper (D 0) (R 0) [50,12,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2464
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 69 328 177 177 241 177 433), lower := (rows 51 14 69 328 16 32 64 128 256), losses := [] }

theorem u2465 : Upper (D 0) (R 0) [50,12,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2465
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2466 : Route 9 := (fun mask => (mask,id))

def c2466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2466 : Upper (D 0) (R 0) [50,12,65,384] 13 := by
  apply FastRouting.sound _ _ [50,12,65,384] 13 (by decide) (choices 1) [1,32,64,128] r2466 c2466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1206
  · exact u1207
  · exact u1208
  · exact u1209

def b2467 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 200 433 417 481 417 417), lower := (rows 51 14 84 200 16 32 64 128 256), losses := [] }

theorem u2467 : Upper (D 0) (R 0) [50,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2467
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 265 241 225 225 225 481), lower := (rows 51 14 84 265 16 32 64 128 256), losses := [] }

theorem u2468 : Upper (D 0) (R 0) [50,12,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2468
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 328 177 161 225 161 417), lower := (rows 51 14 84 328 16 32 64 128 256), losses := [] }

theorem u2469 : Upper (D 0) (R 0) [50,12,80,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2469
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 14 84 392 241 225 225 225 481), lower := (rows 51 14 84 392 16 32 64 128 256), losses := [] }

theorem u2470 : Upper (D 0) (R 0) [50,12,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2470
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 51 14 196 200 305 305 369 433 305), lower := (rows 51 14 196 200 16 32 64 128 256), losses := [] }

theorem u2471 : Upper (D 0) (R 0) [50,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2471
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2472 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2472 : Upper (D 0) (R 0) [50,12,192,257] 13 := by
  apply FastRouting.sound _ _ [50,12,192,257] 13 (by decide) (choices 1) [1,32,64] r2472 c2472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1210
  · exact u1211
  · exact u1212

def b2473 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 51 14 196 280 241 225 225 225 481), lower := (rows 51 14 196 280 16 32 64 128 256), losses := [] }

theorem u2473 : Upper (D 0) (R 0) [50,12,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2473
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 14 196 328 177 177 241 177 433), lower := (rows 51 14 196 328 16 32 64 128 256), losses := [] }

theorem u2474 : Upper (D 0) (R 0) [50,12,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2474
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 13 28 496 480 480 480 480), lower := (rows 51 67 13 28 16 32 64 128 256), losses := [] }

theorem u2475 : Upper (D 0) (R 0) [50,65,9,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2475
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 13 76 432 432 496 432 432), lower := (rows 51 67 13 76 16 32 64 128 256), losses := [] }

theorem u2476 : Upper (D 0) (R 0) [50,65,9,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2476
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 88 436 420 484 420 420), lower := (rows 51 67 13 88 16 32 64 128 256), losses := [] }

theorem u2477 : Upper (D 0) (R 0) [50,65,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2477
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2478 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 140 496 496 496 496 496), lower := (rows 51 67 13 140 16 32 64 128 256), losses := [] }

theorem u2478 : Upper (D 0) (R 0) [50,65,9,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2478
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 484, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 152 500 484 484 484 484), lower := (rows 51 67 13 152 16 32 64 128 256), losses := [] }

theorem u2479 : Upper (D 0) (R 0) [50,65,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2479
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 200 436 436 500 436 436), lower := (rows 51 67 13 200 16 32 64 128 256), losses := [] }

theorem u2480 : Upper (D 0) (R 0) [50,65,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2480
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 268 240 240 240 240 496), lower := (rows 51 67 13 268 16 32 64 128 256), losses := [] }

theorem u2481 : Upper (D 0) (R 0) [50,65,9,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2481
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 228, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 280 244 228 228 228 484), lower := (rows 51 67 13 280 16 32 64 128 256), losses := [] }

theorem u2482 : Upper (D 0) (R 0) [50,65,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2482
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 328 180 180 244 180 436), lower := (rows 51 67 13 328 16 32 64 128 256), losses := [] }

theorem u2483 : Upper (D 0) (R 0) [50,65,9,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2483
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 51 67 13 392 244 244 244 244 500), lower := (rows 51 67 13 392 16 32 64 128 256), losses := [] }

theorem u2484 : Upper (D 0) (R 0) [50,65,9,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2484
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 21 44 472 488 456 456 456), lower := (rows 51 67 21 44 16 32 64 128 256), losses := [] }

theorem u2485 : Upper (D 0) (R 0) [50,65,17,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2485
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 76 440 424 488 424 424), lower := (rows 51 67 21 76 16 32 64 128 256), losses := [] }

theorem u2486 : Upper (D 0) (R 0) [50,65,17,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2486
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 104 412 428 460 396 396), lower := (rows 51 67 21 104 16 32 64 128 256), losses := [] }

theorem u2487 : Upper (D 0) (R 0) [50,65,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2487
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2488 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 140 504 488 488 488 488), lower := (rows 51 67 21 140 16 32 64 128 256), losses := [] }

theorem u2488 : Upper (D 0) (R 0) [50,65,17,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2488
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 460, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 168 476 492 460 460 460), lower := (rows 51 67 21 168 16 32 64 128 256), losses := [] }

theorem u2489 : Upper (D 0) (R 0) [50,65,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2489
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 200 444 428 492 428 428), lower := (rows 51 67 21 200 16 32 64 128 256), losses := [] }

theorem u2490 : Upper (D 0) (R 0) [50,65,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2490
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2491 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 268 248 232 232 232 488), lower := (rows 51 67 21 268 16 32 64 128 256), losses := [] }

theorem u2491 : Upper (D 0) (R 0) [50,65,17,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2491
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2492 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 296 220 236 204 204 460), lower := (rows 51 67 21 296 16 32 64 128 256), losses := [] }

theorem u2492 : Upper (D 0) (R 0) [50,65,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2492
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2493 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 328 188 172 236 172 428), lower := (rows 51 67 21 328 16 32 64 128 256), losses := [] }

theorem u2493 : Upper (D 0) (R 0) [50,65,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2493
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 67 21 392 252 236 236 236 492), lower := (rows 51 67 21 392 16 32 64 128 256), losses := [] }

theorem u2494 : Upper (D 0) (R 0) [50,65,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2494
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 44 465 481 449 449 449), lower := (rows 51 67 28 44 16 32 64 128 256), losses := [] }

theorem u2495 : Upper (D 0) (R 0) [50,65,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2495
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 51 67 28 73 436 420 484 420 420), lower := (rows 51 67 28 73 16 32 64 128 256), losses := [] }

theorem u2496 : Upper (D 0) (R 0) [50,65,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2496
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 76 433 417 481 417 417), lower := (rows 51 67 28 76 16 32 64 128 256), losses := [] }

theorem u2497 : Upper (D 0) (R 0) [50,65,24,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2497
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2498 : Route 9 := (fun mask => (mask,id))

def c2498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | _ => 0)

theorem u2498 : Upper (D 0) (R 0) [50,65,24,96] 13 := by
  apply FastRouting.sound _ _ [50,65,24,96] 13 (by decide) (choices 1) [1,4,128,256] r2498 c2498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1213
  · exact u1214
  · exact u1215
  · exact u1216

def b2499 : PairBound 9 := { available := 484, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 137 500 484 484 484 484), lower := (rows 51 67 28 137 16 32 64 128 256), losses := [] }

theorem u2499 : Upper (D 0) (R 0) [50,65,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2499
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 140 497 481 481 481 481), lower := (rows 51 67 28 140 16 32 64 128 256), losses := [] }

theorem u2500 : Upper (D 0) (R 0) [50,65,24,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2500
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2501 : Route 9 := (fun mask => (mask,id))

def c2501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | _ => 0)

theorem u2501 : Upper (D 0) (R 0) [50,65,24,160] 13 := by
  apply FastRouting.sound _ _ [50,65,24,160] 13 (by decide) (choices 1) [1,4,64,128,256] r2501 c2501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1217
  · exact u1218
  · exact u1219
  · exact u1220
  · exact u1221

def r2502 : Route 9 := (fun mask => (mask,id))

def c2502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | _ => 0)

theorem u2502 : Upper (D 0) (R 0) [50,65,24,192] 13 := by
  apply FastRouting.sound _ _ [50,65,24,192] 13 (by decide) (choices 1) [1,4,32,128,256] r2502 c2502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1222
  · exact u1223
  · exact u1224
  · exact u1225
  · exact u1226

def b2503 : PairBound 9 := { available := 228, camps := [{ cop := 3, region := 244, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 28 265 244 228 228 228 484), lower := (rows 51 67 28 265 16 32 64 128 256), losses := [] }

theorem u2503 : Upper (D 0) (R 0) [50,65,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2503
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 194, targets := 16 }], pairs := [(1,4)], upper := (rows 51 67 28 268 241 225 225 225 481), lower := (rows 51 67 28 268 16 32 64 128 256), losses := [] }

theorem u2504 : Upper (D 0) (R 0) [50,65,24,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2504
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2505 : Route 9 := (fun mask => (mask,id))

def c2505 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u2505 : Upper (D 0) (R 0) [50,65,24,288] 13 := by
  apply FastRouting.sound _ _ [50,65,24,288] 13 (by decide) (choices 1) [1,4,64,128] r2505 c2505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1227
  · exact u1228
  · exact u1229
  · exact u1230

def r2506 : Route 9 := (fun mask => (mask,id))

def c2506 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2506 : Upper (D 0) (R 0) [50,65,24,320] 13 := by
  apply FastRouting.sound _ _ [50,65,24,320] 13 (by decide) (choices 1) [1,4,32,128] r2506 c2506
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1231
  · exact u1232
  · exact u1233
  · exact u1234

def r2507 : Route 9 := (fun mask => (mask,id))

def c2507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2507 : Upper (D 0) (R 0) [50,65,24,384] 13 := by
  apply FastRouting.sound _ _ [50,65,24,384] 13 (by decide) (choices 1) [1,4,32,64,128] r2507 c2507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u1235
  · exact u1236
  · exact u1237
  · exact u1238
  · exact u1239

def b2508 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 76 409 425 457 393 393), lower := (rows 51 67 52 76 16 32 64 128 256), losses := [] }

theorem u2508 : Upper (D 0) (R 0) [50,65,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2508
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 140 473 489 457 457 457), lower := (rows 51 67 52 140 16 32 64 128 256), losses := [] }

theorem u2509 : Upper (D 0) (R 0) [50,65,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2509
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 200 413 429 461 397 397), lower := (rows 51 67 52 200 16 32 64 128 256), losses := [] }

theorem u2510 : Upper (D 0) (R 0) [50,65,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2510
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 268 217 233 201 201 457), lower := (rows 51 67 52 268 16 32 64 128 256), losses := [] }

theorem u2511 : Upper (D 0) (R 0) [50,65,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2511
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 328 157 173 205 141 397), lower := (rows 51 67 52 328 16 32 64 128 256), losses := [] }

theorem u2512 : Upper (D 0) (R 0) [50,65,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2512
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 205, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 52 392 221 237 205 205 461), lower := (rows 51 67 52 392 16 32 64 128 256), losses := [] }

theorem u2513 : Upper (D 0) (R 0) [50,65,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2513
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 440, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 69 140 440 440 504 440 440), lower := (rows 51 67 69 140 16 32 64 128 256), losses := [] }

theorem u2514 : Upper (D 0) (R 0) [50,65,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2514
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 428, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 69 152 444 428 492 428 428), lower := (rows 51 67 69 152 16 32 64 128 256), losses := [] }

theorem u2515 : Upper (D 0) (R 0) [50,65,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2515
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 69 268 184 184 248 184 440), lower := (rows 51 67 69 268 16 32 64 128 256), losses := [] }

theorem u2516 : Upper (D 0) (R 0) [50,65,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2516
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 172, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 69 280 188 172 236 172 428), lower := (rows 51 67 69 280 16 32 64 128 256), losses := [] }

theorem u2517 : Upper (D 0) (R 0) [50,65,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2517
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 67 69 392 188 188 252 188 444), lower := (rows 51 67 69 392 16 32 64 128 256), losses := [] }

theorem u2518 : Upper (D 0) (R 0) [50,65,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2518
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 436, camps := [{ cop := 3, region := 372, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 76 137 436 436 500 436 436), lower := (rows 51 67 76 137 16 32 64 128 256), losses := [] }

theorem u2519 : Upper (D 0) (R 0) [50,65,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2519
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P00
