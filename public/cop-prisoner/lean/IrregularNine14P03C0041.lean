import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0009
import IrregularNine14P03C0010

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 196 88 280 161 225 161 417), lower := (rows 7 35 196 88 280 32 64 128 256), losses := [] }

theorem u2460 : Upper (D 3) (R 3) [6,33,192,80,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2460
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2461 : Route 9 := (fun mask => (mask,id))

def c2461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2461 : Upper (D 3) (R 3) [6,33,192,80,288] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,288] 13 (by decide) (choices 1) [1,8,128] r2461 c2461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u583
  · exact u584
  · exact u585

def r2462 : Route 9 := (fun mask => (mask,id))

def c2462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2462 : Upper (D 3) (R 3) [6,33,192,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,80,384] 13 (by decide) (choices 1) [1,8] r2462 c2462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u586
  · exact u587

def r2463 : Route 9 := (fun mask => (mask,id))

def c2463 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2463 : Upper (D 3) (R 3) [6,33,192,96,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,257] 13 (by decide) (choices 1) [1,8,16,128] r2463 c2463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u588
  · exact u589
  · exact u590
  · exact u591

def r2464 : Route 9 := (fun mask => (mask,id))

def c2464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2464 : Upper (D 3) (R 3) [6,33,192,96,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,264] 13 (by decide) (choices 1) [1,16,128] r2464 c2464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u592
  · exact u593
  · exact u594

def r2465 : Route 9 := (fun mask => (mask,id))

def c2465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2465 : Upper (D 3) (R 3) [6,33,192,96,384] 13 := by
  apply FastRouting.sound _ _ [6,33,192,96,384] 13 (by decide) (choices 1) [1,8,16] r2465 c2465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u595
  · exact u596
  · exact u597

def b2466 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 273 57 121 185 313), lower := (rows 7 35 196 200 273 32 64 128 256), losses := [] }

theorem u2466 : Upper (D 3) (R 3) [6,33,192,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2466
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 280 49 113 177 305), lower := (rows 7 35 196 200 280 32 64 128 256), losses := [] }

theorem u2467 : Upper (D 3) (R 3) [6,33,192,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2467
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 200 304 57 89 153 281), lower := (rows 7 35 196 200 304 32 64 128 256), losses := [] }

theorem u2468 : Upper (D 3) (R 3) [6,33,192,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2468
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 261 25 56 224 192 192 448), lower := (rows 7 35 261 25 56 32 64 128 256), losses := [] }

theorem u2469 : Upper (D 3) (R 3) [6,33,257,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2469
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 25 88 224 224 224 480), lower := (rows 7 35 261 25 88 32 64 128 256), losses := [] }

theorem u2470 : Upper (D 3) (R 3) [6,33,257,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2470
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 200, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 25 112 232 200 200 456), lower := (rows 7 35 261 25 112 32 64 128 256), losses := [] }

theorem u2471 : Upper (D 3) (R 3) [6,33,257,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2471
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 25 208 232 232 232 488), lower := (rows 7 35 261 25 208 32 64 128 256), losses := [] }

theorem u2472 : Upper (D 3) (R 3) [6,33,257,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2472
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 261 41 88 240 208 208 464), lower := (rows 7 35 261 41 88 32 64 128 256), losses := [] }

theorem u2473 : Upper (D 3) (R 3) [6,33,257,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2473
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 261 41 208 248 216 216 472), lower := (rows 7 35 261 41 208 32 64 128 256), losses := [] }

theorem u2474 : Upper (D 3) (R 3) [6,33,257,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2474
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 261 56 81 232 200 200 456), lower := (rows 7 35 261 56 81 32 64 128 256), losses := [] }

theorem u2475 : Upper (D 3) (R 3) [6,33,257,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2475
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 261 56 88 225 193 193 449), lower := (rows 7 35 261 56 88 32 64 128 256), losses := [] }

theorem u2476 : Upper (D 3) (R 3) [6,33,257,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2476
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2477 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2477 : Upper (D 3) (R 3) [6,33,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,48,192] 13 (by decide) (choices 1) [1,8,64] r2477 c2477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u598
  · exact u599
  · exact u600

def b2478 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 73 88 176 240 176 432), lower := (rows 7 35 261 73 88 32 64 128 256), losses := [] }

theorem u2478 : Upper (D 3) (R 3) [6,33,257,65,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2478
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 73 112 184 216 152 408), lower := (rows 7 35 261 73 112 32 64 128 256), losses := [] }

theorem u2479 : Upper (D 3) (R 3) [6,33,257,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2479
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 73 152 240 240 240 496), lower := (rows 7 35 261 73 152 32 64 128 256), losses := [] }

theorem u2480 : Upper (D 3) (R 3) [6,33,257,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2480
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 73 176 248 216 216 472), lower := (rows 7 35 261 73 176 32 64 128 256), losses := [] }

theorem u2481 : Upper (D 3) (R 3) [6,33,257,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2481
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 176, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 73 208 184 248 184 440), lower := (rows 7 35 261 73 208 32 64 128 256), losses := [] }

theorem u2482 : Upper (D 3) (R 3) [6,33,257,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2482
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 161, camps := [{ cop := 6, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 261 88 88 161 225 161 417), lower := (rows 7 35 261 88 88 32 64 128 256), losses := [] }

theorem u2483 : Upper (D 3) (R 3) [6,33,257,80,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2483
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 88 112 169 201 137 393), lower := (rows 7 35 261 88 112 32 64 128 256), losses := [] }

theorem u2484 : Upper (D 3) (R 3) [6,33,257,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2484
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m2485_128 : Upper (D 3) (R 3) [6,33,257,80,136,128] 13 :=
  permutation_upper _ _ _ [6,33,257,80,136,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u602

def r2485 : Route 9 := (fun mask => (mask,id))

def c2485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2485 : Upper (D 3) (R 3) [6,33,257,80,136] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,136] 13 (by decide) (choices 1) [1,64,128] r2485 c2485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u601
  · exact u602
  · exact m2485_128

def r2486 : Route 9 := (fun mask => (mask,id))

def c2486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2486 : Upper (D 3) (R 3) [6,33,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,257,80,160] 13 (by decide) (choices 1) [1,8,64,128] r2486 c2486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u603
  · exact u604
  · exact u605
  · exact u606

def b2487 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 261 88 208 169 233 169 425), lower := (rows 7 35 261 88 208 32 64 128 256), losses := [] }

theorem u2487 : Upper (D 3) (R 3) [6,33,257,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2487
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2488 : Route 9 := (fun mask => (mask,id))

def c2488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2488 : Upper (D 3) (R 3) [6,33,257,96,192] 13 := by
  apply FastRouting.sound _ _ [6,33,257,96,192] 13 (by decide) (choices 1) [1,8,16,128] r2488 c2488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u607
  · exact u608
  · exact u609
  · exact u610

def b2489 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 261 200 208 57 121 185 313), lower := (rows 7 35 261 200 208 32 64 128 256), losses := [] }

theorem u2489 : Upper (D 3) (R 3) [6,33,257,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2489
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 192, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 268 25 49 224 192 192 448), lower := (rows 7 35 268 25 49 32 64 128 256), losses := [] }

theorem u2490 : Upper (D 3) (R 3) [6,33,264,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2490
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2491 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 268 25 81 224 224 224 480), lower := (rows 7 35 268 25 81 32 64 128 256), losses := [] }

theorem u2491 : Upper (D 3) (R 3) [6,33,264,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2491
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2492 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 268 25 112 225 193 193 449), lower := (rows 7 35 268 25 112 32 64 128 256), losses := [] }

theorem u2492 : Upper (D 3) (R 3) [6,33,264,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2492
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2493 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2493 : Upper (D 3) (R 3) [6,33,264,17,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,17,192] 13 (by decide) (choices 1) [1,64] r2493 c2493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u611
  · exact u612

def b2494 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 73 49 240 208 208 464), lower := (rows 7 35 268 73 49 32 64 128 256), losses := [] }

theorem u2494 : Upper (D 3) (R 3) [6,33,264,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2494
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 268 73 81 176 240 176 432), lower := (rows 7 35 268 73 81 32 64 128 256), losses := [] }

theorem u2495 : Upper (D 3) (R 3) [6,33,264,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2495
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2496 : Route 9 := (fun mask => (mask,id))

def c2496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2496 : Upper (D 3) (R 3) [6,33,264,65,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,96] 13 (by decide) (choices 1) [1,16,128] r2496 c2496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u613
  · exact u614
  · exact u615

def r2497 : Route 9 := (fun mask => (mask,id))

def c2497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2497 : Upper (D 3) (R 3) [6,33,264,65,129] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,129] 13 (by decide) (choices 1) [16,64,128] r2497 c2497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u616
  · exact u617
  · exact u618

def r2498 : Route 9 := (fun mask => (mask,id))

def c2498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2498 : Upper (D 3) (R 3) [6,33,264,65,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,160] 13 (by decide) (choices 1) [1,16,64,128] r2498 c2498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u619
  · exact u620
  · exact u621
  · exact u622

def r2499 : Route 9 := (fun mask => (mask,id))

def c2499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2499 : Upper (D 3) (R 3) [6,33,264,65,192] 13 := by
  apply FastRouting.sound _ _ [6,33,264,65,192] 13 (by decide) (choices 1) [1,16,128] r2499 c2499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u623
  · exact u624
  · exact u625

def b2500 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 88 49 225 193 193 449), lower := (rows 7 35 268 88 49 32 64 128 256), losses := [] }

theorem u2500 : Upper (D 3) (R 3) [6,33,264,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 81 161 225 161 417), lower := (rows 7 35 268 88 81 32 64 128 256), losses := [] }

theorem u2501 : Upper (D 3) (R 3) [6,33,264,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2501
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 112 161 193 129 385), lower := (rows 7 35 268 88 112 32 64 128 256), losses := [] }

theorem u2502 : Upper (D 3) (R 3) [6,33,264,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2502
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2503 : Route 9 := (fun mask => (mask,id))

def c2503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2503 : Upper (D 3) (R 3) [6,33,264,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,129] 13 (by decide) (choices 1) [1,64,128] r2503 c2503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u626
  · exact u627
  · exact u628

def r2504 : Route 9 := (fun mask => (mask,id))

def c2504 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2504 : Upper (D 3) (R 3) [6,33,264,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,264,80,160] 13 (by decide) (choices 1) [1,64,128] r2504 c2504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u629
  · exact u630
  · exact u631

def b2505 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 268 88 208 161 225 161 417), lower := (rows 7 35 268 88 208 32 64 128 256), losses := [] }

theorem u2505 : Upper (D 3) (R 3) [6,33,264,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2505
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 16, targets := 64 }], pairs := [(4,6)], upper := (rows 7 35 268 200 49 241 209 209 465), lower := (rows 7 35 268 200 49 32 64 128 256), losses := [] }

theorem u2506 : Upper (D 3) (R 3) [6,33,264,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 268 200 81 177 241 177 433), lower := (rows 7 35 268 200 81 32 64 128 256), losses := [] }

theorem u2507 : Upper (D 3) (R 3) [6,33,264,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2508 : Route 9 := (fun mask => (mask,id))

def c2508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2508 : Upper (D 3) (R 3) [6,33,264,192,96] 13 := by
  apply FastRouting.sound _ _ [6,33,264,192,96] 13 (by decide) (choices 1) [1,16,128] r2508 c2508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u632
  · exact u633
  · exact u634

def b2509 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 268 200 208 49 113 177 305), lower := (rows 7 35 268 200 208 32 64 128 256), losses := [] }

theorem u2509 : Upper (D 3) (R 3) [6,33,264,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 324 25 25 224 224 224 480), lower := (rows 7 35 324 25 25 32 64 128 256), losses := [] }

theorem u2510 : Upper (D 3) (R 3) [6,33,320,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 200, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 25 49 232 200 200 456), lower := (rows 7 35 324 25 49 32 64 128 256), losses := [] }

theorem u2511 : Upper (D 3) (R 3) [6,33,320,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 25 56 225 193 193 449), lower := (rows 7 35 324 25 56 32 64 128 256), losses := [] }

theorem u2512 : Upper (D 3) (R 3) [6,33,320,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 324 25 81 168 232 168 424), lower := (rows 7 35 324 25 81 32 64 128 256), losses := [] }

theorem u2513 : Upper (D 3) (R 3) [6,33,320,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 25 88 161 225 161 417), lower := (rows 7 35 324 25 88 32 64 128 256), losses := [] }

theorem u2514 : Upper (D 3) (R 3) [6,33,320,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 324 25 112 169 201 137 393), lower := (rows 7 35 324 25 112 32 64 128 256), losses := [] }

theorem u2515 : Upper (D 3) (R 3) [6,33,320,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 35 324 25 145 232 232 232 488), lower := (rows 7 35 324 25 145 32 64 128 256), losses := [] }

theorem u2516 : Upper (D 3) (R 3) [6,33,320,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2517 : Route 9 := (fun mask => (mask,id))

def c2517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2517 : Upper (D 3) (R 3) [6,33,320,17,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,17,136] 13 (by decide) (choices 1) [1,64,128] r2517 c2517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u635
  · exact u636
  · exact u637

def b2518 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 35 324 25 176 233 201 201 457), lower := (rows 7 35 324 25 176 32 64 128 256), losses := [] }

theorem u2518 : Upper (D 3) (R 3) [6,33,320,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2518
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 25 208 169 233 169 425), lower := (rows 7 35 324 25 208 32 64 128 256), losses := [] }

theorem u2519 : Upper (D 3) (R 3) [6,33,320,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2519
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P03
