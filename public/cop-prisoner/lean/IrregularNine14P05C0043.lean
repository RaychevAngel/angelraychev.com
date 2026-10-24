import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0009

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2580 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 273 40 101 165 293), lower := (rows 7 42 196 26 273 40 64 128 256), losses := [] }

theorem u2580 : Upper (D 5) (R 5) [6,40,192,18,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2581 : Route 9 := (fun mask => (mask,id))

def c2581 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2581 : Upper (D 5) (R 5) [6,40,192,18,260,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18,260,1] 13 (by decide) (choices 1) [1,8,32] r2581 c2581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u545
  · exact u546
  · exact u547

def b2582 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 26 276 40 97 161 289), lower := (rows 7 42 196 26 276 40 64 128 256), losses := [] }

theorem u2582 : Upper (D 5) (R 5) [6,40,192,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2582
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2583 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 196, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 42 196 28 273 33 106 170 298), lower := (rows 7 42 196 28 273 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 7 24 16 32 66 130 258), good := (rows 454 494 196 28 284 36 64 128 256) }] }

theorem u2583 : Upper (D 5) (R 5) [6,40,192,20,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2584 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 28 273 34 105 169 297), lower := (rows 7 42 196 28 273 34 64 128 256), losses := [] }

theorem u2584 : Upper (D 5) (R 5) [6,40,192,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 28 273 40 99 163 291), lower := (rows 7 42 196 28 273 40 64 128 256), losses := [] }

theorem u2585 : Upper (D 5) (R 5) [6,40,192,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2586 : Route 9 := (fun mask => (mask,id))

def c2586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2586 : Upper (D 5) (R 5) [6,40,192,20,258,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,258,1] 13 (by decide) (choices 1) [1,8,32] r2586 c2586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u548
  · exact u549
  · exact u550

def b2587 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 28 274 40 97 161 289), lower := (rows 7 42 196 28 274 40 64 128 256), losses := [] }

theorem u2587 : Upper (D 5) (R 5) [6,40,192,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2588 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 212, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 42 196 265 28 33 114 178 306), lower := (rows 7 42 196 265 28 33 64 128 256), losses := [] }

theorem u2588 : Upper (D 5) (R 5) [6,40,192,257,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2589 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 265 28 34 113 177 305), lower := (rows 7 42 196 265 28 34 64 128 256), losses := [] }

theorem u2589 : Upper (D 5) (R 5) [6,40,192,257,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2590 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 196 265 28 48 99 163 291), lower := (rows 7 42 196 265 28 48 64 128 256), losses := [] }

theorem u2590 : Upper (D 5) (R 5) [6,40,192,257,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 196 265 49 34 92 156 284), lower := (rows 7 42 196 265 49 34 64 128 256), losses := [] }

theorem u2591 : Upper (D 5) (R 5) [6,40,192,257,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 265 49 36 90 154 282), lower := (rows 7 42 196 265 49 36 64 128 256), losses := [] }

theorem u2592 : Upper (D 5) (R 5) [6,40,192,257,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2593 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 213, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 265 49 40 86 150 278), lower := (rows 7 42 196 265 49 40 64 128 256), losses := [] }

theorem u2593 : Upper (D 5) (R 5) [6,40,192,257,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2594 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 196 265 49 48 78 142 270), lower := (rows 7 42 196 265 49 48 64 128 256), losses := [] }

theorem u2594 : Upper (D 5) (R 5) [6,40,192,257,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 265 52 33 90 154 282), lower := (rows 7 42 196 265 52 33 64 128 256), losses := [] }

theorem u2595 : Upper (D 5) (R 5) [6,40,192,257,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 265 52 34 89 153 281), lower := (rows 7 42 196 265 52 34 64 128 256), losses := [] }

theorem u2596 : Upper (D 5) (R 5) [6,40,192,257,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 213, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 265 52 40 83 147 275), lower := (rows 7 42 196 265 52 40 64 128 256), losses := [] }

theorem u2597 : Upper (D 5) (R 5) [6,40,192,257,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2598 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 265 52 48 75 139 267), lower := (rows 7 42 196 265 52 48 64 128 256), losses := [] }

theorem u2598 : Upper (D 5) (R 5) [6,40,192,257,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2599 : PairBound 9 := { available := 49, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 42 196 266 28 33 113 177 305), lower := (rows 7 42 196 266 28 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 37 8 18 33 65 129 257), good := (rows 501 60 196 280 28 485 64 128 256) }] }

theorem u2599 : Upper (D 5) (R 5) [6,40,192,258,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 196 266 28 48 97 161 289), lower := (rows 7 42 196 266 28 48 64 128 256), losses := [] }

theorem u2600 : Upper (D 5) (R 5) [6,40,192,258,12,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 196 266 49 33 92 156 284), lower := (rows 7 42 196 266 49 33 64 128 256), losses := [] }

theorem u2601 : Upper (D 5) (R 5) [6,40,192,258,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 266 49 36 89 153 281), lower := (rows 7 42 196 266 49 36 64 128 256), losses := [] }

theorem u2602 : Upper (D 5) (R 5) [6,40,192,258,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2603 : PairBound 9 := { available := 21, camps := [{ cop := 8, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 266 49 40 85 149 277), lower := (rows 7 42 196 266 49 40 64 128 256), losses := [] }

theorem u2603 : Upper (D 5) (R 5) [6,40,192,258,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2604 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 196 266 49 48 77 141 269), lower := (rows 7 42 196 266 49 48 64 128 256), losses := [] }

theorem u2604 : Upper (D 5) (R 5) [6,40,192,258,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 196 266 52 33 89 153 281), lower := (rows 7 42 196 266 52 33 64 128 256), losses := [] }

theorem u2605 : Upper (D 5) (R 5) [6,40,192,258,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 17, camps := [{ cop := 8, region := 42, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 266 52 40 81 145 273), lower := (rows 7 42 196 266 52 40 64 128 256), losses := [] }

theorem u2606 : Upper (D 5) (R 5) [6,40,192,258,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 196 266 52 48 73 137 265), lower := (rows 7 42 196 266 52 48 64 128 256), losses := [] }

theorem u2607 : Upper (D 5) (R 5) [6,40,192,258,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2608 : Route 9 := (fun mask => (mask,id))

def c2608 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2608 : Upper (D 5) (R 5) [6,40,192,260,9,1] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260,9,1] 13 (by decide) (choices 1) [2,16,32] r2608 c2608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u551
  · exact u552
  · exact u553

def b2609 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 196 268 25 34 113 177 305), lower := (rows 7 42 196 268 25 34 64 128 256), losses := [] }

theorem u2609 : Upper (D 5) (R 5) [6,40,192,260,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 197, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 196 268 25 48 99 163 291), lower := (rows 7 42 196 268 25 48 64 128 256), losses := [] }

theorem u2610 : Upper (D 5) (R 5) [6,40,192,260,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 48, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 7 42 196 268 49 33 90 154 282), lower := (rows 7 42 196 268 49 33 64 128 256), losses := [] }

theorem u2611 : Upper (D 5) (R 5) [6,40,192,260,33,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 460, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 196 268 49 34 89 153 281), lower := (rows 7 42 196 268 49 34 64 128 256), losses := [] }

theorem u2612 : Upper (D 5) (R 5) [6,40,192,260,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 213, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 42 196 268 49 40 83 147 275), lower := (rows 7 42 196 268 49 40 64 128 256), losses := [] }

theorem u2613 : Upper (D 5) (R 5) [6,40,192,260,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 196 268 49 48 75 139 267), lower := (rows 7 42 196 268 49 48 64 128 256), losses := [] }

theorem u2614 : Upper (D 5) (R 5) [6,40,192,260,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 69 41 152 34 332 396 268), lower := (rows 7 50 69 41 152 34 64 128 256), losses := [] }

theorem u2615 : Upper (D 5) (R 5) [6,48,65,33,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 41 152 36 330 394 266), lower := (rows 7 50 69 41 152 36 64 128 256), losses := [] }

theorem u2616 : Upper (D 5) (R 5) [6,48,65,33,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 325, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 69 41 152 40 326 390 262), lower := (rows 7 50 69 41 152 40 64 128 256), losses := [] }

theorem u2617 : Upper (D 5) (R 5) [6,48,65,33,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2618 : Route 9 := (fun mask => (mask,id))

def c2618 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2618 : Upper (D 5) (R 5) [6,48,65,33,136,256] 13 := by
  apply FastRouting.sound _ _ [6,48,65,33,136,256] 13 (by decide) (choices 1) [2,4,8] r2618 c2618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u554
  · exact u555
  · exact u556

def b2619 : PairBound 9 := { available := 12, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 69 41 400 34 76 140 268), lower := (rows 7 50 69 41 400 34 64 128 256), losses := [] }

theorem u2619 : Upper (D 5) (R 5) [6,48,65,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2620 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 41 400 36 74 138 266), lower := (rows 7 50 69 41 400 36 64 128 256), losses := [] }

theorem u2620 : Upper (D 5) (R 5) [6,48,65,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2621 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 50 69 41 400 40 78 142 270), lower := (rows 7 50 69 41 400 40 64 128 256), losses := [] }

theorem u2621 : Upper (D 5) (R 5) [6,48,65,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2622 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 152 33 330 394 266), lower := (rows 7 50 69 44 152 33 64 128 256), losses := [] }

theorem u2622 : Upper (D 5) (R 5) [6,48,65,36,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 152 34 329 393 265), lower := (rows 7 50 69 44 152 34 64 128 256), losses := [] }

theorem u2623 : Upper (D 5) (R 5) [6,48,65,36,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 69 44 152 40 323 387 259), lower := (rows 7 50 69 44 152 40 64 128 256), losses := [] }

theorem u2624 : Upper (D 5) (R 5) [6,48,65,36,136,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2625 : Route 9 := (fun mask => (mask,id))

def c2625 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2625 : Upper (D 5) (R 5) [6,48,65,36,136,256] 13 := by
  apply FastRouting.sound _ _ [6,48,65,36,136,256] 13 (by decide) (choices 1) [1,2,8] r2625 c2625
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u557
  · exact u558
  · exact u559

def b2626 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 402, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 400 33 74 138 266), lower := (rows 7 50 69 44 400 33 64 128 256), losses := [] }

theorem u2626 : Upper (D 5) (R 5) [6,48,65,36,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 44 400 34 73 137 265), lower := (rows 7 50 69 44 400 34 64 128 256), losses := [] }

theorem u2627 : Upper (D 5) (R 5) [6,48,65,36,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 50 69 44 400 40 75 139 267), lower := (rows 7 50 69 44 400 40 64 128 256), losses := [] }

theorem u2628 : Upper (D 5) (R 5) [6,48,65,36,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 137 280 34 108 172 300), lower := (rows 7 50 69 137 280 34 64 128 256), losses := [] }

theorem u2629 : Upper (D 5) (R 5) [6,48,65,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(4,0)], upper := (rows 7 50 69 137 280 36 106 170 298), lower := (rows 7 50 69 137 280 36 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 24 37 72 136 264), good := (rows 38 50 100 506 474 36 64 128 256) }] }

theorem u2630 : Upper (D 5) (R 5) [6,48,65,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 69 137 280 40 102 166 294), lower := (rows 7 50 69 137 280 40 64 128 256), losses := [] }

theorem u2631 : Upper (D 5) (R 5) [6,48,65,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2632 : Route 9 := (fun mask => (mask,id))

def c2632 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2632 : Upper (D 5) (R 5) [6,48,65,130,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,65,130,264,1] 13 (by decide) (choices 1) [4,8,32] r2632 c2632
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u560
  · exact u561
  · exact u562

def r2633 : Route 9 := (fun mask => (mask,id))

def c2633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2633 : Upper (D 5) (R 5) [6,48,65,130,264,4] 13 := by
  apply FastRouting.sound _ _ [6,48,65,130,264,4] 13 (by decide) (choices 1) [1,8,32] r2633 c2633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u563
  · exact u564
  · exact u565

def b2634 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 69 138 280 40 101 165 293), lower := (rows 7 50 69 138 280 40 64 128 256), losses := [] }

theorem u2634 : Upper (D 5) (R 5) [6,48,65,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 42, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 50 69 140 280 33 106 170 298), lower := (rows 7 50 69 140 280 33 64 128 256), losses := [{ target := 2, region := (rows 1 10 0 8 24 37 72 136 264), good := (rows 35 50 97 506 474 33 64 128 256) }] }

theorem u2635 : Upper (D 5) (R 5) [6,48,65,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 140 280 34 105 169 297), lower := (rows 7 50 69 140 280 34 64 128 256), losses := [] }

theorem u2636 : Upper (D 5) (R 5) [6,48,65,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 69 140 280 40 99 163 291), lower := (rows 7 50 69 140 280 40 64 128 256), losses := [] }

theorem u2637 : Upper (D 5) (R 5) [6,48,65,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 392, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 50 69 168 28 33 330 394 266), lower := (rows 7 50 69 168 28 33 64 128 256), losses := [] }

theorem u2638 : Upper (D 5) (R 5) [6,48,65,160,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 28 34 329 393 265), lower := (rows 7 50 69 168 28 34 64 128 256), losses := [] }

theorem u2639 : Upper (D 5) (R 5) [6,48,65,160,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2639
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P05
