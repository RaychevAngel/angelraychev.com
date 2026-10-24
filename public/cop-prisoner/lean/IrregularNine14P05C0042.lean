import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0008
import IrregularNine14P05C0009

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 76 137 304 33 86 150 278), lower := (rows 7 42 76 137 304 33 64 128 256), losses := [] }

theorem u2520 : Upper (D 5) (R 5) [6,40,72,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2520
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 137 304 34 85 149 277), lower := (rows 7 42 76 137 304 34 64 128 256), losses := [] }

theorem u2521 : Upper (D 5) (R 5) [6,40,72,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2521
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2522 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 137 304 36 83 147 275), lower := (rows 7 42 76 137 304 36 64 128 256), losses := [] }

theorem u2522 : Upper (D 5) (R 5) [6,40,72,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2522
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 7, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 76 137 304 48 71 135 263), lower := (rows 7 42 76 137 304 48 64 128 256), losses := [] }

theorem u2523 : Upper (D 5) (R 5) [6,40,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2523
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 1, region := 68, targets := 1 }], pairs := [(2,0),(4,3)], upper := (rows 7 42 76 152 273 33 102 166 294), lower := (rows 7 42 76 152 273 33 64 128 256), losses := [] }

theorem u2524 : Upper (D 5) (R 5) [6,40,72,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2524
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 152 273 34 101 165 293), lower := (rows 7 42 76 152 273 34 64 128 256), losses := [] }

theorem u2525 : Upper (D 5) (R 5) [6,40,72,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2525
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2526 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 152 273 36 99 163 291), lower := (rows 7 42 76 152 273 36 64 128 256), losses := [] }

theorem u2526 : Upper (D 5) (R 5) [6,40,72,144,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2526
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2527 : Route 9 := (fun mask => (mask,id))

def c2527 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2527 : Upper (D 5) (R 5) [6,40,72,144,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144,258,1] 13 (by decide) (choices 1) [1,4,32] r2527 c2527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u516
  · exact u517
  · exact u518

def b2528 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 304, targets := 8 },{ cop := 2, region := 34, targets := 1 }], pairs := [(1,0),(4,3)], upper := (rows 7 42 76 152 274 36 97 161 289), lower := (rows 7 42 76 152 274 36 64 128 256), losses := [] }

theorem u2528 : Upper (D 5) (R 5) [6,40,72,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2528
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2529 : Route 9 := (fun mask => (mask,id))

def c2529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2529 : Upper (D 5) (R 5) [6,40,72,144,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,72,144,260,1] 13 (by decide) (choices 1) [1,2,32] r2529 c2529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u519
  · exact u520
  · exact u521

def b2530 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 76 152 276 34 97 161 289), lower := (rows 7 42 76 152 276 34 64 128 256), losses := [] }

theorem u2530 : Upper (D 5) (R 5) [6,40,72,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2530
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 22, camps := [{ cop := 4, region := 462, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 42 76 392 49 33 86 150 278), lower := (rows 7 42 76 392 49 33 64 128 256), losses := [] }

theorem u2531 : Upper (D 5) (R 5) [6,40,72,384,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2531
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2532 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 76 392 49 34 85 149 277), lower := (rows 7 42 76 392 49 34 64 128 256), losses := [] }

theorem u2532 : Upper (D 5) (R 5) [6,40,72,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2532
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2533 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 394, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 76 392 49 36 83 147 275), lower := (rows 7 42 76 392 49 36 64 128 256), losses := [] }

theorem u2533 : Upper (D 5) (R 5) [6,40,72,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2533
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2534 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 76 392 49 48 71 135 263), lower := (rows 7 42 76 392 49 48 64 128 256), losses := [] }

theorem u2534 : Upper (D 5) (R 5) [6,40,72,384,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2534
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2535 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 48, targets := 2 },{ cop := 0, region := 48, targets := 8 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 76 392 52 33 83 147 275), lower := (rows 7 42 76 392 52 33 64 128 256), losses := [] }

theorem u2535 : Upper (D 5) (R 5) [6,40,72,384,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2535
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2536 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 76 392 52 34 81 145 273), lower := (rows 7 42 76 392 52 34 64 128 256), losses := [] }

theorem u2536 : Upper (D 5) (R 5) [6,40,72,384,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2536
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2537 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 76 392 52 48 67 131 259), lower := (rows 7 42 76 392 52 48 64 128 256), losses := [] }

theorem u2537 : Upper (D 5) (R 5) [6,40,72,384,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2537
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 137 273 34 108 172 300), lower := (rows 7 42 84 137 273 34 64 128 256), losses := [] }

theorem u2538 : Upper (D 5) (R 5) [6,40,80,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2538
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2539 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(3,2)], upper := (rows 7 42 84 137 273 36 106 170 298), lower := (rows 7 42 84 137 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 74 138 266), good := (rows 486 490 116 490 304 36 64 128 256) },{ target := 2, region := (rows 1 2 0 9 17 32 66 130 258), good := (rows 475 490 80 153 281 32 64 128 256) }] }

theorem u2539 : Upper (D 5) (R 5) [6,40,80,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2539
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2540 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 137 273 40 102 166 294), lower := (rows 7 42 84 137 273 40 64 128 256), losses := [] }

theorem u2540 : Upper (D 5) (R 5) [6,40,80,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2540
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2541 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 84 137 274 33 108 172 300), lower := (rows 7 42 84 137 274 33 64 128 256), losses := [] }

theorem u2541 : Upper (D 5) (R 5) [6,40,80,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2541
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 168, targets := 2 }], pairs := [(1,0),(3,1)], upper := (rows 7 42 84 137 274 36 105 169 297), lower := (rows 7 42 84 137 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 116 170 274 36 64 128 256) }] }

theorem u2542 : Upper (D 5) (R 5) [6,40,80,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2542
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 137 274 40 101 165 293), lower := (rows 7 42 84 137 274 40 64 128 256), losses := [] }

theorem u2543 : Upper (D 5) (R 5) [6,40,80,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2543
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2544 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 84 137 280 33 102 166 294), lower := (rows 7 42 84 137 280 33 64 128 256), losses := [] }

theorem u2544 : Upper (D 5) (R 5) [6,40,80,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2544
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2545 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 137 280 34 101 165 293), lower := (rows 7 42 84 137 280 34 64 128 256), losses := [] }

theorem u2545 : Upper (D 5) (R 5) [6,40,80,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2545
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2546 : Route 9 := (fun mask => (mask,id))

def c2546 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2546 : Upper (D 5) (R 5) [6,40,80,129,264,4] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,264,4] 13 (by decide) (choices 1) [1,2,32] r2546 c2546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u522
  · exact u523
  · exact u524

def b2547 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 340, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 84 137 304 33 78 142 270), lower := (rows 7 42 84 137 304 33 64 128 256), losses := [] }

theorem u2547 : Upper (D 5) (R 5) [6,40,80,129,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2547
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 84 137 304 34 77 141 269), lower := (rows 7 42 84 137 304 34 64 128 256), losses := [] }

theorem u2548 : Upper (D 5) (R 5) [6,40,80,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2548
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 137 304 36 75 139 267), lower := (rows 7 42 84 137 304 36 64 128 256), losses := [] }

theorem u2549 : Upper (D 5) (R 5) [6,40,80,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2549
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 137 304 40 71 135 263), lower := (rows 7 42 84 137 304 40 64 128 256), losses := [] }

theorem u2550 : Upper (D 5) (R 5) [6,40,80,129,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2550
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2551 : Route 9 := (fun mask => (mask,id))

def c2551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2551 : Upper (D 5) (R 5) [6,40,80,130,257,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,257,1] 13 (by decide) (choices 1) [4,8,32] r2551 c2551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u525
  · exact u526
  · exact u527

def r2552 : Route 9 := (fun mask => (mask,id))

def c2552 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2552 : Upper (D 5) (R 5) [6,40,80,130,257,4] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,257,4] 13 (by decide) (choices 1) [1,8,32] r2552 c2552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u528
  · exact u529
  · exact u530

def b2553 : PairBound 9 := { available := 37, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 138 273 40 101 165 293), lower := (rows 7 42 84 138 273 40 64 128 256), losses := [] }

theorem u2553 : Upper (D 5) (R 5) [6,40,80,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2553
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 42 84 138 280 33 101 165 293), lower := (rows 7 42 84 138 280 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 7 8 18 33 97 161 289), good := (rows 501 508 84 156 280 485 64 128 256) }] }

theorem u2554 : Upper (D 5) (R 5) [6,40,80,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2554
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2555 : Route 9 := (fun mask => (mask,id))

def c2555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2555 : Upper (D 5) (R 5) [6,40,80,130,264,4] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,264,4] 13 (by decide) (choices 1) [1,32] r2555 c2555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u531
  · exact u532

def r2556 : Route 9 := (fun mask => (mask,id))

def c2556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2556 : Upper (D 5) (R 5) [6,40,80,130,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,288,1] 13 (by decide) (choices 1) [1,4,8] r2556 c2556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b2557 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 84 138 304 36 73 137 265), lower := (rows 7 42 84 138 304 36 64 128 256), losses := [] }

theorem u2557 : Upper (D 5) (R 5) [6,40,80,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2557
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2558 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 138 304 40 69 133 261), lower := (rows 7 42 84 138 304 40 64 128 256), losses := [] }

theorem u2558 : Upper (D 5) (R 5) [6,40,80,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2558
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 84 140 273 33 106 170 298), lower := (rows 7 42 84 140 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 34 4 9 16 32 98 162 290), good := (rows 462 490 84 140 280 490 64 128 256) }] }

theorem u2559 : Upper (D 5) (R 5) [6,40,80,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2559
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 140 273 34 105 169 297), lower := (rows 7 42 84 140 273 34 64 128 256), losses := [] }

theorem u2560 : Upper (D 5) (R 5) [6,40,80,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 140 273 40 99 163 291), lower := (rows 7 42 84 140 273 40 64 128 256), losses := [] }

theorem u2561 : Upper (D 5) (R 5) [6,40,80,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2562 : Route 9 := (fun mask => (mask,id))

def c2562 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2562 : Upper (D 5) (R 5) [6,40,80,132,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,258,1] 13 (by decide) (choices 1) [1,8,32] r2562 c2562
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def b2563 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 140 274 40 97 161 289), lower := (rows 7 42 84 140 274 40 64 128 256), losses := [] }

theorem u2563 : Upper (D 5) (R 5) [6,40,80,132,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2564 : Route 9 := (fun mask => (mask,id))

def c2564 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2564 : Upper (D 5) (R 5) [6,40,80,132,264,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,264,1] 13 (by decide) (choices 1) [1,2,32] r2564 c2564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u539
  · exact u540
  · exact u541

def b2565 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 140 280 34 97 161 289), lower := (rows 7 42 84 140 280 34 64 128 256), losses := [] }

theorem u2565 : Upper (D 5) (R 5) [6,40,80,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2566 : Route 9 := (fun mask => (mask,id))

def c2566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2566 : Upper (D 5) (R 5) [6,40,80,132,288,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,288,1] 13 (by decide) (choices 1) [1,2,8] r2566 c2566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def b2567 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 42 84 140 304 34 73 137 265), lower := (rows 7 42 84 140 304 34 64 128 256), losses := [] }

theorem u2567 : Upper (D 5) (R 5) [6,40,80,132,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 341, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 84 140 304 40 67 131 259), lower := (rows 7 42 84 140 304 40 64 128 256), losses := [] }

theorem u2568 : Upper (D 5) (R 5) [6,40,80,132,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 34, targets := 4 }], pairs := [(1,2),(2,3)], upper := (rows 7 42 84 392 25 33 102 166 294), lower := (rows 7 42 84 392 25 33 64 128 256), losses := [{ target := 3, region := (rows 1 2 20 0 16 49 65 129 257), good := (rows 487 34 116 384 501 481 64 128 256) }] }

theorem u2569 : Upper (D 5) (R 5) [6,40,80,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 84 392 25 34 101 165 293), lower := (rows 7 42 84 392 25 34 64 128 256), losses := [] }

theorem u2570 : Upper (D 5) (R 5) [6,40,80,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 35, camps := [], pairs := [(1,0),(2,3)], upper := (rows 7 42 84 392 25 36 99 163 291), lower := (rows 7 42 84 392 25 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 42 118 392 58 36 64 128 256) },{ target := 3, region := (rows 1 2 20 0 16 53 65 129 257), good := (rows 487 34 116 384 501 36 64 128 256) }] }

theorem u2571 : Upper (D 5) (R 5) [6,40,80,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 196 25 274 33 108 172 300), lower := (rows 7 42 196 25 274 33 64 128 256), losses := [] }

theorem u2572 : Upper (D 5) (R 5) [6,40,192,17,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 228, targets := 2 }], pairs := [(1,0),(2,1)], upper := (rows 7 42 196 25 274 36 105 169 297), lower := (rows 7 42 196 25 274 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 37 64 128 256), good := (rows 38 42 228 58 274 36 64 128 256) }] }

theorem u2573 : Upper (D 5) (R 5) [6,40,192,17,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2574 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 25 274 40 101 165 293), lower := (rows 7 42 196 25 274 40 64 128 256), losses := [] }

theorem u2574 : Upper (D 5) (R 5) [6,40,192,17,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2575 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 196 25 276 33 106 170 298), lower := (rows 7 42 196 25 276 33 64 128 256), losses := [] }

theorem u2575 : Upper (D 5) (R 5) [6,40,192,17,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 34, targets := 1 },{ cop := 3, region := 34, targets := 4 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 25 276 34 105 169 297), lower := (rows 7 42 196 25 276 34 64 128 256), losses := [] }

theorem u2576 : Upper (D 5) (R 5) [6,40,192,17,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2576
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 25 276 40 99 163 291), lower := (rows 7 42 196 25 276 40 64 128 256), losses := [] }

theorem u2577 : Upper (D 5) (R 5) [6,40,192,17,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 42, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 42 196 26 273 33 108 172 300), lower := (rows 7 42 196 26 273 33 64 128 256), losses := [] }

theorem u2578 : Upper (D 5) (R 5) [6,40,192,18,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0),(3,0)], upper := (rows 7 42 196 26 273 36 105 169 297), lower := (rows 7 42 196 26 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 24 16 37 64 128 256), good := (rows 38 42 228 26 314 36 64 128 256) }] }

theorem u2579 : Upper (D 5) (R 5) [6,40,192,18,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2579
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P05
