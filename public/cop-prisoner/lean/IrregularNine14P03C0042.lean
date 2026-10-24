import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0010
import IrregularNine14P03C0011

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2520 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 88 177 209 145 401), lower := (rows 7 35 324 41 88 32 64 128 256), losses := [] }

theorem u2520 : Upper (D 3) (R 3) [6,33,320,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2520
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2521 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 145 248 216 216 472), lower := (rows 7 35 324 41 145 32 64 128 256), losses := [] }

theorem u2521 : Upper (D 3) (R 3) [6,33,320,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2521
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2522 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 152 241 209 209 465), lower := (rows 7 35 324 41 152 32 64 128 256), losses := [] }

theorem u2522 : Upper (D 3) (R 3) [6,33,320,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2522
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2523 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 7 35 324 41 208 185 217 153 409), lower := (rows 7 35 324 41 208 32 64 128 256), losses := [] }

theorem u2523 : Upper (D 3) (R 3) [6,33,320,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2523
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2524 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 56 81 169 201 137 393), lower := (rows 7 35 324 56 81 32 64 128 256), losses := [] }

theorem u2524 : Upper (D 3) (R 3) [6,33,320,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2524
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2525 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 324 56 88 161 193 129 385), lower := (rows 7 35 324 56 88 32 64 128 256), losses := [] }

theorem u2525 : Upper (D 3) (R 3) [6,33,320,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2525
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2526 : Route 9 := (fun mask => (mask,id))

def c2526 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2526 : Upper (D 3) (R 3) [6,33,320,48,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,129] 13 (by decide) (choices 1) [1,8,64,128] r2526 c2526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u638
  · exact u639
  · exact u640
  · exact u641

def b2527 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 35 324 56 152 225 193 193 449), lower := (rows 7 35 324 56 152 32 64 128 256), losses := [] }

theorem u2527 : Upper (D 3) (R 3) [6,33,320,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2527
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2528 : Route 9 := (fun mask => (mask,id))

def c2528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2528 : Upper (D 3) (R 3) [6,33,320,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,48,192] 13 (by decide) (choices 1) [1,8,128] r2528 c2528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u642
  · exact u643
  · exact u644

def b2529 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 73 145 184 248 184 440), lower := (rows 7 35 324 73 145 32 64 128 256), losses := [] }

theorem u2529 : Upper (D 3) (R 3) [6,33,320,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2529
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2530 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 73 152 177 241 177 433), lower := (rows 7 35 324 73 152 32 64 128 256), losses := [] }

theorem u2530 : Upper (D 3) (R 3) [6,33,320,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2530
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2531 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6)], upper := (rows 7 35 324 73 176 185 217 153 409), lower := (rows 7 35 324 73 176 32 64 128 256), losses := [] }

theorem u2531 : Upper (D 3) (R 3) [6,33,320,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2531
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2532 : Route 9 := (fun mask => (mask,id))

def c2532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2532 : Upper (D 3) (R 3) [6,33,320,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,129] 13 (by decide) (choices 1) [1,8,128] r2532 c2532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u645
  · exact u646
  · exact u647

def b2533 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 324 88 152 161 225 161 417), lower := (rows 7 35 324 88 152 32 64 128 256), losses := [] }

theorem u2533 : Upper (D 3) (R 3) [6,33,320,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2533
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2534 : Route 9 := (fun mask => (mask,id))

def c2534 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2534 : Upper (D 3) (R 3) [6,33,320,80,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,80,160] 13 (by decide) (choices 1) [1,8,128] r2534 c2534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u648
  · exact u649
  · exact u650

def r2535 : Route 9 := (fun mask => (mask,id))

def c2535 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2535 : Upper (D 3) (R 3) [6,33,320,96,129] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,129] 13 (by decide) (choices 1) [1,8,16,128] r2535 c2535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u651
  · exact u652
  · exact u653
  · exact u654

def r2536 : Route 9 := (fun mask => (mask,id))

def c2536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2536 : Upper (D 3) (R 3) [6,33,320,96,136] 13 := by
  apply FastRouting.sound _ _ [6,33,320,96,136] 13 (by decide) (choices 1) [1,16,128] r2536 c2536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u655
  · exact u656
  · exact u657

def b2537 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 35 324 137 145 120 120 248 376), lower := (rows 7 35 324 137 145 32 64 128 256), losses := [] }

theorem u2537 : Upper (D 3) (R 3) [6,33,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2538 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 324 137 152 113 113 241 369), lower := (rows 7 35 324 137 152 32 64 128 256), losses := [] }

theorem u2538 : Upper (D 3) (R 3) [6,33,320,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2538
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2539 : Route 9 := (fun mask => (mask,id))

def c2539 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2539 : Upper (D 3) (R 3) [6,33,320,129,160] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,160] 13 (by decide) (choices 1) [1,8,16,64] r2539 c2539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u658
  · exact u659
  · exact u660
  · exact u661

def r2540 : Route 9 := (fun mask => (mask,id))

def c2540 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2540 : Upper (D 3) (R 3) [6,33,320,129,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,129,192] 13 (by decide) (choices 1) [1,8,16] r2540 c2540
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u662
  · exact u663
  · exact u664

def b2541 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 324 152 152 97 97 225 353), lower := (rows 7 35 324 152 152 32 64 128 256), losses := [] }

theorem u2541 : Upper (D 3) (R 3) [6,33,320,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2542 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 152 176 105 73 201 329), lower := (rows 7 35 324 152 176 32 64 128 256), losses := [] }

theorem u2542 : Upper (D 3) (R 3) [6,33,320,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2543 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 35 324 152 208 41 105 169 297), lower := (rows 7 35 324 152 208 32 64 128 256), losses := [] }

theorem u2543 : Upper (D 3) (R 3) [6,33,320,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2544 : Route 9 := (fun mask => (mask,id))

def c2544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2544 : Upper (D 3) (R 3) [6,33,320,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,320,160,192] 13 (by decide) (choices 1) [1,8,16] r2544 c2544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u665
  · exact u666
  · exact u667

def b2545 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 41 145 481 449 449 449), lower := (rows 7 42 84 41 145 32 64 128 256), losses := [] }

theorem u2545 : Upper (D 3) (R 3) [6,40,80,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2546 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 41 273 225 193 193 449), lower := (rows 7 42 84 41 273 32 64 128 256), losses := [] }

theorem u2546 : Upper (D 3) (R 3) [6,40,80,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2547 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 41 400 225 193 193 449), lower := (rows 7 42 84 41 400 32 64 128 256), losses := [] }

theorem u2547 : Upper (D 3) (R 3) [6,40,80,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2548 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 73 145 417 481 417 417), lower := (rows 7 42 84 73 145 32 64 128 256), losses := [] }

theorem u2548 : Upper (D 3) (R 3) [6,40,80,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2549 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 73 273 161 225 161 417), lower := (rows 7 42 84 73 273 32 64 128 256), losses := [] }

theorem u2549 : Upper (D 3) (R 3) [6,40,80,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2550 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 84 73 400 161 225 161 417), lower := (rows 7 42 84 73 400 32 64 128 256), losses := [] }

theorem u2550 : Upper (D 3) (R 3) [6,40,80,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2550
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2551 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 104 145 417 449 385 385), lower := (rows 7 42 84 104 145 32 64 128 256), losses := [] }

theorem u2551 : Upper (D 3) (R 3) [6,40,80,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2552 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 104 273 161 193 129 385), lower := (rows 7 42 84 104 273 32 64 128 256), losses := [] }

theorem u2552 : Upper (D 3) (R 3) [6,40,80,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2552
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2553 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 104 400 161 193 129 385), lower := (rows 7 42 84 104 400 32 64 128 256), losses := [] }

theorem u2553 : Upper (D 3) (R 3) [6,40,80,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2554 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 84 137 145 353 353 481 353), lower := (rows 7 42 84 137 145 32 64 128 256), losses := [] }

theorem u2554 : Upper (D 3) (R 3) [6,40,80,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2555 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 84 137 176 353 321 449 321), lower := (rows 7 42 84 137 176 32 64 128 256), losses := [] }

theorem u2555 : Upper (D 3) (R 3) [6,40,80,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2556 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 208 289 353 417 289), lower := (rows 7 42 84 137 208 32 64 128 256), losses := [] }

theorem u2556 : Upper (D 3) (R 3) [6,40,80,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2557 : Route 9 := (fun mask => (mask,id))

def c2557 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2557 : Upper (D 3) (R 3) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [1,64,128] r2557 c2557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u668
  · exact u669
  · exact u670

def b2558 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 84 137 304 225 193 193 449), lower := (rows 7 42 84 137 304 32 64 128 256), losses := [] }

theorem u2558 : Upper (D 3) (R 3) [6,40,80,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2559 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 336 161 225 161 417), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u2559 : Upper (D 3) (R 3) [6,40,80,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2559
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2560 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 84 137 400 97 97 225 353), lower := (rows 7 42 84 137 400 32 64 128 256), losses := [] }

theorem u2560 : Upper (D 3) (R 3) [6,40,80,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2561 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 168 273 225 193 193 449), lower := (rows 7 42 84 168 273 32 64 128 256), losses := [] }

theorem u2561 : Upper (D 3) (R 3) [6,40,80,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2562 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 84 168 400 97 65 193 321), lower := (rows 7 42 84 168 400 32 64 128 256), losses := [] }

theorem u2562 : Upper (D 3) (R 3) [6,40,80,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2563 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 273 161 225 161 417), lower := (rows 7 42 84 200 273 32 64 128 256), losses := [] }

theorem u2563 : Upper (D 3) (R 3) [6,40,80,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2564 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 7 42 84 200 400 33 97 161 289), lower := (rows 7 42 84 200 400 32 64 128 256), losses := [] }

theorem u2564 : Upper (D 3) (R 3) [6,40,80,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2565 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 25 49 481 449 449 449), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u2565 : Upper (D 3) (R 3) [6,40,192,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2566 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 196 25 81 417 481 417 417), lower := (rows 7 42 196 25 81 32 64 128 256), losses := [] }

theorem u2566 : Upper (D 3) (R 3) [6,40,192,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2567 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 25 112 417 449 385 385), lower := (rows 7 42 196 25 112 32 64 128 256), losses := [] }

theorem u2567 : Upper (D 3) (R 3) [6,40,192,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2568 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 25 208 289 353 417 289), lower := (rows 7 42 196 25 208 32 64 128 256), losses := [] }

theorem u2568 : Upper (D 3) (R 3) [6,40,192,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2569 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 196 25 273 225 225 225 481), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u2569 : Upper (D 3) (R 3) [6,40,192,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2570 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 25 304 225 193 193 449), lower := (rows 7 42 196 25 304 32 64 128 256), losses := [] }

theorem u2570 : Upper (D 3) (R 3) [6,40,192,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2571 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 25 336 161 225 161 417), lower := (rows 7 42 196 25 336 32 64 128 256), losses := [] }

theorem u2571 : Upper (D 3) (R 3) [6,40,192,17,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2572 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 196, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 196 265 49 241 209 209 465), lower := (rows 7 42 196 265 49 32 64 128 256), losses := [] }

theorem u2572 : Upper (D 3) (R 3) [6,40,192,257,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2572
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2573 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 265 81 177 241 177 433), lower := (rows 7 42 196 265 81 32 64 128 256), losses := [] }

theorem u2573 : Upper (D 3) (R 3) [6,40,192,257,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2574 : Route 9 := (fun mask => (mask,id))

def c2574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2574 : Upper (D 3) (R 3) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [1,16,128] r2574 c2574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u671
  · exact u672
  · exact u673

def b2575 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 265 208 49 113 177 305), lower := (rows 7 42 196 265 208 32 64 128 256), losses := [] }

theorem u2575 : Upper (D 3) (R 3) [6,40,192,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2576 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 280 49 225 193 193 449), lower := (rows 7 42 196 280 49 32 64 128 256), losses := [] }

theorem u2576 : Upper (D 3) (R 3) [6,40,192,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2577 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 280 81 161 225 161 417), lower := (rows 7 42 196 280 81 32 64 128 256), losses := [] }

theorem u2577 : Upper (D 3) (R 3) [6,40,192,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2578 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 280 112 161 193 129 385), lower := (rows 7 42 196 280 112 32 64 128 256), losses := [] }

theorem u2578 : Upper (D 3) (R 3) [6,40,192,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2579 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 280 208 33 97 161 289), lower := (rows 7 42 196 280 208 32 64 128 256), losses := [] }

theorem u2579 : Upper (D 3) (R 3) [6,40,192,272,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2579
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2579
end Delivery.IrregularNine14.P03
