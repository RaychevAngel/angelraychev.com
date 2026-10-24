import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0008
import IrregularNine14P01C0009

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 152 48 482 450 450 450), lower := (rows 51 7 76 152 48 32 64 128 256), losses := [] }

theorem u2460 : Upper (D 1) (R 1) [50,5,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2461 : PairBound 9 := { available := 418, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 152 80 418 482 418 418), lower := (rows 51 7 76 152 80 32 64 128 256), losses := [] }

theorem u2461 : Upper (D 1) (R 1) [50,5,72,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 354, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 76 152 144 354 354 482 354), lower := (rows 51 7 76 152 144 32 64 128 256), losses := [] }

theorem u2462 : Upper (D 1) (R 1) [50,5,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 7 76 152 272 226 226 226 482), lower := (rows 51 7 76 152 272 32 64 128 256), losses := [] }

theorem u2463 : Upper (D 1) (R 1) [50,5,72,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 280 18 224 224 224 480), lower := (rows 51 7 76 280 18 32 64 128 256), losses := [] }

theorem u2464 : Upper (D 1) (R 1) [50,5,72,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2464
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 280 48 226 194 194 450), lower := (rows 51 7 76 280 48 32 64 128 256), losses := [] }

theorem u2465 : Upper (D 1) (R 1) [50,5,72,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2465
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 280 80 162 226 162 418), lower := (rows 51 7 76 280 80 32 64 128 256), losses := [] }

theorem u2466 : Upper (D 1) (R 1) [50,5,72,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2466
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2467 : Route 9 := (fun mask => (mask,id))

def c2467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2467 : Upper (D 1) (R 1) [50,5,72,272,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,272,128] 13 (by decide) (choices 1) [2,64,128] r2467 c2467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def b2468 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 76 392 18 240 240 240 496), lower := (rows 51 7 76 392 18 32 64 128 256), losses := [] }

theorem u2468 : Upper (D 1) (R 1) [50,5,72,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 76 392 48 242 210 210 466), lower := (rows 51 7 76 392 48 32 64 128 256), losses := [] }

theorem u2469 : Upper (D 1) (R 1) [50,5,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 76 392 80 178 242 178 434), lower := (rows 51 7 76 392 80 32 64 128 256), losses := [] }

theorem u2470 : Upper (D 1) (R 1) [50,5,72,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2470
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2471_2 : Upper (D 1) (R 1) [50,5,72,384,128,2] 13 :=
  permutation_upper _ _ _ [50,5,72,384,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u539

theorem m2471_16 : Upper (D 1) (R 1) [50,5,72,384,128,16] 13 :=
  permutation_upper _ _ _ [50,5,72,384,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u540

theorem m2471_64 : Upper (D 1) (R 1) [50,5,72,384,128,64] 13 :=
  permutation_upper _ _ _ [50,5,72,384,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u541

def r2471 : Route 9 := (fun mask => (mask,id))

def c2471 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2471 : Upper (D 1) (R 1) [50,5,72,384,128] 13 := by
  apply FastRouting.sound _ _ [50,5,72,384,128] 13 (by decide) (choices 1) [2,16,64] r2471 c2471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2471_2
  · exact m2471_16
  · exact m2471_64

def b2472 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 196 88 18 424 488 424 424), lower := (rows 51 7 196 88 18 32 64 128 256), losses := [] }

theorem u2472 : Upper (D 1) (R 1) [50,5,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2472
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 51 7 196 88 24 418 482 418 418), lower := (rows 51 7 196 88 24 32 64 128 256), losses := [] }

theorem u2473 : Upper (D 1) (R 1) [50,5,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2473
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 394, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 88 48 426 458 394 394), lower := (rows 51 7 196 88 48 32 64 128 256), losses := [] }

theorem u2474 : Upper (D 1) (R 1) [50,5,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2474
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 298, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 51 7 196 88 144 298 362 426 298), lower := (rows 51 7 196 88 144 32 64 128 256), losses := [] }

theorem u2475 : Upper (D 1) (R 1) [50,5,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2475
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 7 196 88 272 170 234 170 426), lower := (rows 51 7 196 88 272 32 64 128 256), losses := [] }

theorem u2476 : Upper (D 1) (R 1) [50,5,192,80,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2476
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 196 280 18 232 232 232 488), lower := (rows 51 7 196 280 18 32 64 128 256), losses := [] }

theorem u2477 : Upper (D 1) (R 1) [50,5,192,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2477
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2478 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 7 196 280 24 226 226 226 482), lower := (rows 51 7 196 280 24 32 64 128 256), losses := [] }

theorem u2478 : Upper (D 1) (R 1) [50,5,192,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2478
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 280 48 234 202 202 458), lower := (rows 51 7 196 280 48 32 64 128 256), losses := [] }

theorem u2479 : Upper (D 1) (R 1) [50,5,192,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2479
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2480 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 196 280 80 170 234 170 426), lower := (rows 51 7 196 280 80 32 64 128 256), losses := [] }

theorem u2480 : Upper (D 1) (R 1) [50,5,192,272,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2480
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2481 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 196 328 18 184 248 184 440), lower := (rows 51 7 196 328 18 32 64 128 256), losses := [] }

theorem u2481 : Upper (D 1) (R 1) [50,5,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2481
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 7 196 328 24 178 242 178 434), lower := (rows 51 7 196 328 24 32 64 128 256), losses := [] }

theorem u2482 : Upper (D 1) (R 1) [50,5,192,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2482
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 196 328 48 186 218 154 410), lower := (rows 51 7 196 328 48 32 64 128 256), losses := [] }

theorem u2483 : Upper (D 1) (R 1) [50,5,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2483
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 51 7 196 328 144 58 122 186 314), lower := (rows 51 7 196 328 144 32 64 128 256), losses := [] }

theorem u2484 : Upper (D 1) (R 1) [50,5,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2484
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 88 18 224 224 224 480), lower := (rows 51 7 268 88 18 32 64 128 256), losses := [] }

theorem u2485 : Upper (D 1) (R 1) [50,5,264,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2485
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 88 48 226 194 194 450), lower := (rows 51 7 268 88 48 32 64 128 256), losses := [] }

theorem u2486 : Upper (D 1) (R 1) [50,5,264,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2486
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 51 7 268 88 80 162 226 162 418), lower := (rows 51 7 268 88 80 32 64 128 256), losses := [] }

theorem u2487 : Upper (D 1) (R 1) [50,5,264,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2487
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2488 : Route 9 := (fun mask => (mask,id))

def c2488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2488 : Upper (D 1) (R 1) [50,5,264,80,128] 13 := by
  apply FastRouting.sound _ _ [50,5,264,80,128] 13 (by decide) (choices 1) [2,64,128] r2488 c2488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def b2489 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 268 200 18 240 240 240 496), lower := (rows 51 7 268 200 18 32 64 128 256), losses := [] }

theorem u2489 : Upper (D 1) (R 1) [50,5,264,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2489
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 268 200 48 242 210 210 466), lower := (rows 51 7 268 200 48 32 64 128 256), losses := [] }

theorem u2490 : Upper (D 1) (R 1) [50,5,264,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2490
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2491_2 : Upper (D 1) (R 1) [50,5,264,192,64,2] 13 :=
  permutation_upper _ _ _ [50,5,264,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u545

theorem m2491_16 : Upper (D 1) (R 1) [50,5,264,192,64,16] 13 :=
  permutation_upper _ _ _ [50,5,264,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u546

def r2491 : Route 9 := (fun mask => (mask,id))

def c2491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2491 : Upper (D 1) (R 1) [50,5,264,192,64] 13 := by
  apply FastRouting.sound _ _ [50,5,264,192,64] 13 (by decide) (choices 1) [2,16,128] r2491 c2491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2491_2
  · exact m2491_16
  · exact u547

def b2492 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 88 18 168 232 168 424), lower := (rows 51 7 324 88 18 32 64 128 256), losses := [] }

theorem u2492 : Upper (D 1) (R 1) [50,5,320,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2492
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2493 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 51 7 324 88 24 162 226 162 418), lower := (rows 51 7 324 88 24 32 64 128 256), losses := [] }

theorem u2493 : Upper (D 1) (R 1) [50,5,320,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2493
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 88 48 170 202 138 394), lower := (rows 51 7 324 88 48 32 64 128 256), losses := [] }

theorem u2494 : Upper (D 1) (R 1) [50,5,320,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2494
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2495 : Route 9 := (fun mask => (mask,id))

def c2495 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2495 : Upper (D 1) (R 1) [50,5,320,80,128] 13 := by
  apply FastRouting.sound _ _ [50,5,320,80,128] 13 (by decide) (choices 1) [2,8,128] r2495 c2495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u548
  · exact u549
  · exact u550

def b2496 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 152 18 232 232 232 488), lower := (rows 51 7 324 152 18 32 64 128 256), losses := [] }

theorem u2496 : Upper (D 1) (R 1) [50,5,320,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2496
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 51 7 324 152 24 226 226 226 482), lower := (rows 51 7 324 152 24 32 64 128 256), losses := [] }

theorem u2497 : Upper (D 1) (R 1) [50,5,320,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2497
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2498 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 152 48 234 202 202 458), lower := (rows 51 7 324 152 48 32 64 128 256), losses := [] }

theorem u2498 : Upper (D 1) (R 1) [50,5,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2498
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2499 : PairBound 9 := { available := 170, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 51 7 324 152 80 170 234 170 426), lower := (rows 51 7 324 152 80 32 64 128 256), losses := [] }

theorem u2499 : Upper (D 1) (R 1) [50,5,320,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2499
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 7 324 152 144 106 106 234 362), lower := (rows 51 7 324 152 144 32 64 128 256), losses := [] }

theorem u2500 : Upper (D 1) (R 1) [50,5,320,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 7 324 200 18 184 248 184 440), lower := (rows 51 7 324 200 18 32 64 128 256), losses := [] }

theorem u2501 : Upper (D 1) (R 1) [50,5,320,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 7 324 200 24 178 242 178 434), lower := (rows 51 7 324 200 24 32 64 128 256), losses := [] }

theorem u2502 : Upper (D 1) (R 1) [50,5,320,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 7 324 200 48 186 218 154 410), lower := (rows 51 7 324 200 48 32 64 128 256), losses := [] }

theorem u2503 : Upper (D 1) (R 1) [50,5,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2503
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2504_2 : Upper (D 1) (R 1) [50,5,320,192,128,2] 13 :=
  permutation_upper _ _ _ [50,5,320,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u551

theorem m2504_8 : Upper (D 1) (R 1) [50,5,320,192,128,8] 13 :=
  permutation_upper _ _ _ [50,5,320,192,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u552

theorem m2504_16 : Upper (D 1) (R 1) [50,5,320,192,128,16] 13 :=
  permutation_upper _ _ _ [50,5,320,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u553

def r2504 : Route 9 := (fun mask => (mask,id))

def c2504 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2504 : Upper (D 1) (R 1) [50,5,320,192,128] 13 := by
  apply FastRouting.sound _ _ [50,5,320,192,128] 13 (by decide) (choices 1) [2,8,16] r2504 c2504
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2504_2
  · exact m2504_8
  · exact m2504_16

def b2505 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 69 392 18 240 240 240 496), lower := (rows 51 14 69 392 18 32 64 128 256), losses := [] }

theorem u2505 : Upper (D 1) (R 1) [50,12,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 69 392 48 242 210 210 466), lower := (rows 51 14 69 392 48 32 64 128 256), losses := [] }

theorem u2506 : Upper (D 1) (R 1) [50,12,65,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 69 392 80 178 242 178 434), lower := (rows 51 14 69 392 80 32 64 128 256), losses := [] }

theorem u2507 : Upper (D 1) (R 1) [50,12,65,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 114, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 51 14 69 392 144 114 114 242 370), lower := (rows 51 14 69 392 144 32 64 128 256), losses := [] }

theorem u2508 : Upper (D 1) (R 1) [50,12,65,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 196, targets := 2 }], pairs := [(2,1)], upper := (rows 51 14 196 265 18 240 240 240 496), lower := (rows 51 14 196 265 18 32 64 128 256), losses := [] }

theorem u2509 : Upper (D 1) (R 1) [50,12,192,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 14 196 265 48 242 210 210 466), lower := (rows 51 14 196 265 48 32 64 128 256), losses := [] }

theorem u2510 : Upper (D 1) (R 1) [50,12,192,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 51 14 196 265 80 178 242 178 434), lower := (rows 51 14 196 265 80 32 64 128 256), losses := [] }

theorem u2511 : Upper (D 1) (R 1) [50,12,192,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 388, camps := [{ cop := 3, region := 19, targets := 128 }], pairs := [(0,7)], upper := (rows 51 67 28 104 18 420 452 388 388), lower := (rows 51 67 28 104 18 32 64 128 256), losses := [] }

theorem u2512 : Upper (D 1) (R 1) [50,65,24,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 386, camps := [], pairs := [], upper := (rows 51 67 28 104 20 418 450 386 386), lower := (rows 51 67 28 104 20 32 64 128 256), losses := [] }

theorem u2513 : Upper (D 1) (R 1) [50,65,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2514 : Route 9 := (fun mask => (mask,id))

def c2514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u2514 : Upper (D 1) (R 1) [50,65,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,65,24,96,128] 13 (by decide) (choices 1) [2,4,128,256] r2514 c2514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u554
  · exact u555
  · exact u556
  · exact u557

def b2515 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 67 28 104 272 166 198 134 390), lower := (rows 51 67 28 104 272 32 64 128 256), losses := [] }

theorem u2515 : Upper (D 1) (R 1) [50,65,24,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2515
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 452, camps := [{ cop := 0, region := 460, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 168 18 484 452 452 452), lower := (rows 51 67 28 168 18 32 64 128 256), losses := [] }

theorem u2516 : Upper (D 1) (R 1) [50,65,24,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 51 67 28 168 20 482 450 450 450), lower := (rows 51 67 28 168 20 32 64 128 256), losses := [] }

theorem u2517 : Upper (D 1) (R 1) [50,65,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 67 28 168 80 422 454 390 390), lower := (rows 51 67 28 168 80 32 64 128 256), losses := [] }

theorem u2518 : Upper (D 1) (R 1) [50,65,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 326, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 67 28 168 144 358 326 454 326), lower := (rows 51 67 28 168 144 32 64 128 256), losses := [] }

theorem u2519 : Upper (D 1) (R 1) [50,65,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2519
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P01
