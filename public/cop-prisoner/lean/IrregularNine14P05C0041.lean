import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0008

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2460 : PairBound 9 := { available := 280, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 69 140 49 34 344 408 280), lower := (rows 7 42 69 140 49 34 64 128 256), losses := [] }

theorem u2460 : Upper (D 5) (R 5) [6,40,65,132,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2461 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 140 49 40 338 402 274), lower := (rows 7 42 69 140 49 40 64 128 256), losses := [] }

theorem u2461 : Upper (D 5) (R 5) [6,40,65,132,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2462 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 140 49 48 330 394 266), lower := (rows 7 42 69 140 49 48 64 128 256), losses := [] }

theorem u2462 : Upper (D 5) (R 5) [6,40,65,132,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2463 : Route 9 := (fun mask => (mask,id))

def c2463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2463 : Upper (D 5) (R 5) [6,40,65,132,33,256] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,33,256] 13 (by decide) (choices 1) [2,8,16] r2463 c2463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u504
  · exact u505
  · exact u506

def b2464 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 140 273 34 120 184 312), lower := (rows 7 42 69 140 273 34 64 128 256), losses := [] }

theorem u2464 : Upper (D 5) (R 5) [6,40,65,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 140 273 40 114 178 306), lower := (rows 7 42 69 140 273 40 64 128 256), losses := [] }

theorem u2465 : Upper (D 5) (R 5) [6,40,65,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0)], upper := (rows 7 42 69 140 273 48 106 170 298), lower := (rows 7 42 69 140 273 48 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 9 16 48 82 146 274), good := (rows 462 490 76 140 506 498 64 128 256) }] }

theorem u2466 : Upper (D 5) (R 5) [6,40,65,132,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 274 33 120 184 312), lower := (rows 7 42 69 140 274 33 64 128 256), losses := [] }

theorem u2467 : Upper (D 5) (R 5) [6,40,65,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 140 274 40 113 177 305), lower := (rows 7 42 69 140 274 40 64 128 256), losses := [] }

theorem u2468 : Upper (D 5) (R 5) [6,40,65,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2469 : Route 9 := (fun mask => (mask,id))

def c2469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2469 : Upper (D 5) (R 5) [6,40,65,132,258,16] 13 := by
  apply FastRouting.sound _ _ [6,40,65,132,258,16] 13 (by decide) (choices 1) [1,8,32] r2469 c2469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u507
  · exact u508
  · exact u509

def b2470 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 280 33 114 178 306), lower := (rows 7 42 69 140 280 33 64 128 256), losses := [] }

theorem u2470 : Upper (D 5) (R 5) [6,40,65,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2471 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 140 280 34 113 177 305), lower := (rows 7 42 69 140 280 34 64 128 256), losses := [] }

theorem u2471 : Upper (D 5) (R 5) [6,40,65,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2472 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 140 280 48 99 163 291), lower := (rows 7 42 69 140 280 48 64 128 256), losses := [] }

theorem u2472 : Upper (D 5) (R 5) [6,40,65,132,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2473 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 272, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 42 69 140 304 33 90 154 282), lower := (rows 7 42 69 140 304 33 64 128 256), losses := [] }

theorem u2473 : Upper (D 5) (R 5) [6,40,65,132,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2474 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 140 304 34 89 153 281), lower := (rows 7 42 69 140 304 34 64 128 256), losses := [] }

theorem u2474 : Upper (D 5) (R 5) [6,40,65,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2475 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 140 304 40 83 147 275), lower := (rows 7 42 69 140 304 40 64 128 256), losses := [] }

theorem u2475 : Upper (D 5) (R 5) [6,40,65,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 11, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 69 140 304 48 75 139 267), lower := (rows 7 42 69 140 304 48 64 128 256), losses := [] }

theorem u2476 : Upper (D 5) (R 5) [6,40,65,132,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2477 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 152 273 34 108 172 300), lower := (rows 7 42 69 152 273 34 64 128 256), losses := [] }

theorem u2477 : Upper (D 5) (R 5) [6,40,65,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2478 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 152 273 36 106 170 298), lower := (rows 7 42 69 152 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 82 146 274), good := (rows 486 490 100 474 506 36 64 128 256) }] }

theorem u2478 : Upper (D 5) (R 5) [6,40,65,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2479 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 273 40 102 166 294), lower := (rows 7 42 69 152 273 40 64 128 256), losses := [] }

theorem u2479 : Upper (D 5) (R 5) [6,40,65,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2479
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2480 : Route 9 := (fun mask => (mask,id))

def c2480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2480 : Upper (D 5) (R 5) [6,40,65,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,258,1] 13 (by decide) (choices 1) [4,8,32] r2480 c2480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u510
  · exact u511
  · exact u512

def r2481 : Route 9 := (fun mask => (mask,id))

def c2481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2481 : Upper (D 5) (R 5) [6,40,65,144,258,4] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,258,4] 13 (by decide) (choices 1) [1,8,32] r2481 c2481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u513
  · exact u514
  · exact u515

def b2482 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 274 40 101 165 293), lower := (rows 7 42 69 152 274 40 64 128 256), losses := [] }

theorem u2482 : Upper (D 5) (R 5) [6,40,65,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2482
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2483 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 152 276 33 106 170 298), lower := (rows 7 42 69 152 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 41 17 32 98 162 290), good := (rows 478 490 92 152 276 506 64 128 256) }] }

theorem u2483 : Upper (D 5) (R 5) [6,40,65,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2483
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2484 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 152 276 34 105 169 297), lower := (rows 7 42 69 152 276 34 64 128 256), losses := [] }

theorem u2484 : Upper (D 5) (R 5) [6,40,65,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2484
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2485 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 152 276 40 99 163 291), lower := (rows 7 42 69 152 276 40 64 128 256), losses := [] }

theorem u2485 : Upper (D 5) (R 5) [6,40,65,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2485
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2486 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 25 34 116 180 308), lower := (rows 7 42 69 392 25 34 64 128 256), losses := [] }

theorem u2486 : Upper (D 5) (R 5) [6,40,65,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2486
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2487 : PairBound 9 := { available := 50, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 392 25 36 114 178 306), lower := (rows 7 42 69 392 25 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 80 144 272), good := (rows 38 42 100 392 506 36 64 128 256) }] }

theorem u2487 : Upper (D 5) (R 5) [6,40,65,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2487
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2488 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 392 25 48 102 166 294), lower := (rows 7 42 69 392 25 48 64 128 256), losses := [] }

theorem u2488 : Upper (D 5) (R 5) [6,40,65,384,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2488
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2489 : PairBound 9 := { available := 50, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 69 392 28 33 114 178 306), lower := (rows 7 42 69 392 28 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 42 17 32 96 160 288), good := (rows 30 490 84 392 28 506 64 128 256) }] }

theorem u2489 : Upper (D 5) (R 5) [6,40,65,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2489
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2490 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 28 34 113 177 305), lower := (rows 7 42 69 392 28 34 64 128 256), losses := [] }

theorem u2490 : Upper (D 5) (R 5) [6,40,65,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2490
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2491 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 392 28 48 99 163 291), lower := (rows 7 42 69 392 28 48 64 128 256), losses := [] }

theorem u2491 : Upper (D 5) (R 5) [6,40,65,384,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2491
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2492 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 69 392 49 34 92 156 284), lower := (rows 7 42 69 392 49 34 64 128 256), losses := [] }

theorem u2492 : Upper (D 5) (R 5) [6,40,65,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2492
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2493 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 394, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 49 36 90 154 282), lower := (rows 7 42 69 392 49 36 64 128 256), losses := [] }

theorem u2493 : Upper (D 5) (R 5) [6,40,65,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2493
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2494 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 85, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 392 49 40 86 150 278), lower := (rows 7 42 69 392 49 40 64 128 256), losses := [] }

theorem u2494 : Upper (D 5) (R 5) [6,40,65,384,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2494
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2495 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 392 49 48 78 142 270), lower := (rows 7 42 69 392 49 48 64 128 256), losses := [] }

theorem u2495 : Upper (D 5) (R 5) [6,40,65,384,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2495
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2496 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 394, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 52 33 90 154 282), lower := (rows 7 42 69 392 52 33 64 128 256), losses := [] }

theorem u2496 : Upper (D 5) (R 5) [6,40,65,384,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2496
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2497 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 392 52 34 89 153 281), lower := (rows 7 42 69 392 52 34 64 128 256), losses := [] }

theorem u2497 : Upper (D 5) (R 5) [6,40,65,384,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2497
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2498 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 85, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 69 392 52 40 83 147 275), lower := (rows 7 42 69 392 52 40 64 128 256), losses := [] }

theorem u2498 : Upper (D 5) (R 5) [6,40,65,384,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2498
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2499 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 69 392 52 48 75 139 267), lower := (rows 7 42 69 392 52 48 64 128 256), losses := [] }

theorem u2499 : Upper (D 5) (R 5) [6,40,65,384,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2499
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2500 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 76 25 400 33 102 166 294), lower := (rows 7 42 76 25 400 33 64 128 256), losses := [] }

theorem u2500 : Upper (D 5) (R 5) [6,40,72,17,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2500
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2501 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 25 400 34 101 165 293), lower := (rows 7 42 76 25 400 34 64 128 256), losses := [] }

theorem u2501 : Upper (D 5) (R 5) [6,40,72,17,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2501
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2502 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 432, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 25 400 36 99 163 291), lower := (rows 7 42 76 25 400 36 64 128 256), losses := [] }

theorem u2502 : Upper (D 5) (R 5) [6,40,72,17,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2502
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2503 : PairBound 9 := { available := 276, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 76 137 49 34 340 404 276), lower := (rows 7 42 76 137 49 34 64 128 256), losses := [] }

theorem u2503 : Upper (D 5) (R 5) [6,40,72,129,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2503
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2504 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 394, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 76 137 49 36 338 402 274), lower := (rows 7 42 76 137 49 36 64 128 256), losses := [] }

theorem u2504 : Upper (D 5) (R 5) [6,40,72,129,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2504
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2505 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 76 137 49 48 326 390 262), lower := (rows 7 42 76 137 49 48 64 128 256), losses := [] }

theorem u2505 : Upper (D 5) (R 5) [6,40,72,129,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2505
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2506 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 49 288 86 150 278), lower := (rows 7 42 76 137 49 288 64 128 256), losses := [] }

theorem u2506 : Upper (D 5) (R 5) [6,40,72,129,33,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2506
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2507 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 76 137 52 33 338 402 274), lower := (rows 7 42 76 137 52 33 64 128 256), losses := [] }

theorem u2507 : Upper (D 5) (R 5) [6,40,72,129,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2507
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2508 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 76 137 52 34 337 401 273), lower := (rows 7 42 76 137 52 34 64 128 256), losses := [] }

theorem u2508 : Upper (D 5) (R 5) [6,40,72,129,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2508
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2509 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 76 137 52 48 323 387 259), lower := (rows 7 42 76 137 52 48 64 128 256), losses := [] }

theorem u2509 : Upper (D 5) (R 5) [6,40,72,129,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2509
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2510 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 52 288 83 147 275), lower := (rows 7 42 76 137 52 288 64 128 256), losses := [] }

theorem u2510 : Upper (D 5) (R 5) [6,40,72,129,36,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2510
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2511 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 137 273 34 116 180 308), lower := (rows 7 42 76 137 273 34 64 128 256), losses := [] }

theorem u2511 : Upper (D 5) (R 5) [6,40,72,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2511
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2512 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 137 273 36 114 178 306), lower := (rows 7 42 76 137 273 36 64 128 256), losses := [] }

theorem u2512 : Upper (D 5) (R 5) [6,40,72,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2512
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2513 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 273 48 102 166 294), lower := (rows 7 42 76 137 273 48 64 128 256), losses := [] }

theorem u2513 : Upper (D 5) (R 5) [6,40,72,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2513
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2514 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 76 137 274 33 116 180 308), lower := (rows 7 42 76 137 274 33 64 128 256), losses := [] }

theorem u2514 : Upper (D 5) (R 5) [6,40,72,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2514
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2515 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 137 274 36 113 177 305), lower := (rows 7 42 76 137 274 36 64 128 256), losses := [] }

theorem u2515 : Upper (D 5) (R 5) [6,40,72,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2515
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2516 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 274 48 101 165 293), lower := (rows 7 42 76 137 274 48 64 128 256), losses := [] }

theorem u2516 : Upper (D 5) (R 5) [6,40,72,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2516
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2517 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 76 137 276 33 114 178 306), lower := (rows 7 42 76 137 276 33 64 128 256), losses := [] }

theorem u2517 : Upper (D 5) (R 5) [6,40,72,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2517
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2518 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 137 276 34 113 177 305), lower := (rows 7 42 76 137 276 34 64 128 256), losses := [] }

theorem u2518 : Upper (D 5) (R 5) [6,40,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2518
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2519 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 304, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 276 48 99 163 291), lower := (rows 7 42 76 137 276 48 64 128 256), losses := [] }

theorem u2519 : Upper (D 5) (R 5) [6,40,72,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2519
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P05
