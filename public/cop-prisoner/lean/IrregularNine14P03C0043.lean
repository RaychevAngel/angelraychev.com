import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0011

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2580 : PairBound 9 := { available := 192, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 261 25 49 224 192 192 448), lower := (rows 7 42 261 25 49 32 64 128 256), losses := [] }

theorem u2580 : Upper (D 3) (R 3) [6,40,257,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2581 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 261 25 81 224 224 224 480), lower := (rows 7 42 261 25 81 32 64 128 256), losses := [] }

theorem u2581 : Upper (D 3) (R 3) [6,40,257,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2582 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 25 112 225 193 193 449), lower := (rows 7 42 261 25 112 32 64 128 256), losses := [] }

theorem u2582 : Upper (D 3) (R 3) [6,40,257,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2583 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2583 : Upper (D 3) (R 3) [6,40,257,17,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,17,192] 13 (by decide) (choices 1) [1,64] r2583 c2583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u674
  · exact u675

def b2584 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 261 73 49 240 208 208 464), lower := (rows 7 42 261 73 49 32 64 128 256), losses := [] }

theorem u2584 : Upper (D 3) (R 3) [6,40,257,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2584
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2585 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 261 73 81 176 240 176 432), lower := (rows 7 42 261 73 81 32 64 128 256), losses := [] }

theorem u2585 : Upper (D 3) (R 3) [6,40,257,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2586 : Route 9 := (fun mask => (mask,id))

def c2586 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2586 : Upper (D 3) (R 3) [6,40,257,65,96] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,96] 13 (by decide) (choices 1) [1,16,128] r2586 c2586
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u676
  · exact u677
  · exact u678

def r2587 : Route 9 := (fun mask => (mask,id))

def c2587 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2587 : Upper (D 3) (R 3) [6,40,257,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,129] 13 (by decide) (choices 1) [16,64,128] r2587 c2587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u679
  · exact u680
  · exact u681

def r2588 : Route 9 := (fun mask => (mask,id))

def c2588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2588 : Upper (D 3) (R 3) [6,40,257,65,160] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,160] 13 (by decide) (choices 1) [1,16,64,128] r2588 c2588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u682
  · exact u683
  · exact u684
  · exact u685

def r2589 : Route 9 := (fun mask => (mask,id))

def c2589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2589 : Upper (D 3) (R 3) [6,40,257,65,192] 13 := by
  apply FastRouting.sound _ _ [6,40,257,65,192] 13 (by decide) (choices 1) [1,16,128] r2589 c2589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688

def b2590 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 88 49 225 193 193 449), lower := (rows 7 42 261 88 49 32 64 128 256), losses := [] }

theorem u2590 : Upper (D 3) (R 3) [6,40,257,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2591 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 81 161 225 161 417), lower := (rows 7 42 261 88 81 32 64 128 256), losses := [] }

theorem u2591 : Upper (D 3) (R 3) [6,40,257,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2592 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 88 112 161 193 129 385), lower := (rows 7 42 261 88 112 32 64 128 256), losses := [] }

theorem u2592 : Upper (D 3) (R 3) [6,40,257,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2593 : Route 9 := (fun mask => (mask,id))

def c2593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2593 : Upper (D 3) (R 3) [6,40,257,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80,129] 13 (by decide) (choices 1) [1,64,128] r2593 c2593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u689
  · exact u690
  · exact u691

def b2594 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 261 88 176 225 193 193 449), lower := (rows 7 42 261 88 176 32 64 128 256), losses := [] }

theorem u2594 : Upper (D 3) (R 3) [6,40,257,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2595 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 208 161 225 161 417), lower := (rows 7 42 261 88 208 32 64 128 256), losses := [] }

theorem u2595 : Upper (D 3) (R 3) [6,40,257,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2596 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 261 200 49 241 209 209 465), lower := (rows 7 42 261 200 49 32 64 128 256), losses := [] }

theorem u2596 : Upper (D 3) (R 3) [6,40,257,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2597 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 42 261 200 81 177 241 177 433), lower := (rows 7 42 261 200 81 32 64 128 256), losses := [] }

theorem u2597 : Upper (D 3) (R 3) [6,40,257,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2598 : Route 9 := (fun mask => (mask,id))

def c2598 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2598 : Upper (D 3) (R 3) [6,40,257,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,96] 13 (by decide) (choices 1) [1,16,128] r2598 c2598
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u692
  · exact u693
  · exact u694

def b2599 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 261 200 208 49 113 177 305), lower := (rows 7 42 261 200 208 32 64 128 256), losses := [] }

theorem u2599 : Upper (D 3) (R 3) [6,40,257,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2599
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2600 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 276 73 49 225 193 193 449), lower := (rows 7 42 276 73 49 32 64 128 256), losses := [] }

theorem u2600 : Upper (D 3) (R 3) [6,40,272,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2601 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 276 73 81 161 225 161 417), lower := (rows 7 42 276 73 81 32 64 128 256), losses := [] }

theorem u2601 : Upper (D 3) (R 3) [6,40,272,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2602 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 276 73 112 161 193 129 385), lower := (rows 7 42 276 73 112 32 64 128 256), losses := [] }

theorem u2602 : Upper (D 3) (R 3) [6,40,272,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2603 : Route 9 := (fun mask => (mask,id))

def c2603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2603 : Upper (D 3) (R 3) [6,40,272,65,129] 13 := by
  apply FastRouting.sound _ _ [6,40,272,65,129] 13 (by decide) (choices 1) [1,64,128] r2603 c2603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u695
  · exact u696
  · exact u697

def b2604 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 276 73 176 225 193 193 449), lower := (rows 7 42 276 73 176 32 64 128 256), losses := [] }

theorem u2604 : Upper (D 3) (R 3) [6,40,272,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2605 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 276 73 208 161 225 161 417), lower := (rows 7 42 276 73 208 32 64 128 256), losses := [] }

theorem u2605 : Upper (D 3) (R 3) [6,40,272,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2606 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 276 200 49 225 193 193 449), lower := (rows 7 42 276 200 49 32 64 128 256), losses := [] }

theorem u2606 : Upper (D 3) (R 3) [6,40,272,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2607 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 420, targets := 64 }], pairs := [(2,6)], upper := (rows 7 42 276 200 81 161 225 161 417), lower := (rows 7 42 276 200 81 32 64 128 256), losses := [] }

theorem u2607 : Upper (D 3) (R 3) [6,40,272,192,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2608 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 276 200 112 161 193 129 385), lower := (rows 7 42 276 200 112 32 64 128 256), losses := [] }

theorem u2608 : Upper (D 3) (R 3) [6,40,272,192,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2609 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 276 200 208 33 97 161 289), lower := (rows 7 42 276 200 208 32 64 128 256), losses := [] }

theorem u2609 : Upper (D 3) (R 3) [6,40,272,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2610 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 25 49 225 193 193 449), lower := (rows 7 42 324 25 49 32 64 128 256), losses := [] }

theorem u2610 : Upper (D 3) (R 3) [6,40,320,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2611 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 324 25 81 161 225 161 417), lower := (rows 7 42 324 25 81 32 64 128 256), losses := [] }

theorem u2611 : Upper (D 3) (R 3) [6,40,320,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2612 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 25 112 161 193 129 385), lower := (rows 7 42 324 25 112 32 64 128 256), losses := [] }

theorem u2612 : Upper (D 3) (R 3) [6,40,320,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2613 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 324 25 145 225 225 225 481), lower := (rows 7 42 324 25 145 32 64 128 256), losses := [] }

theorem u2613 : Upper (D 3) (R 3) [6,40,320,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2614 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 25 176 225 193 193 449), lower := (rows 7 42 324 25 176 32 64 128 256), losses := [] }

theorem u2614 : Upper (D 3) (R 3) [6,40,320,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2615 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 25 208 161 225 161 417), lower := (rows 7 42 324 25 208 32 64 128 256), losses := [] }

theorem u2615 : Upper (D 3) (R 3) [6,40,320,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2615
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2616 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 42 324 137 49 241 209 209 465), lower := (rows 7 42 324 137 49 32 64 128 256), losses := [] }

theorem u2616 : Upper (D 3) (R 3) [6,40,320,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2617 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 137 81 177 241 177 433), lower := (rows 7 42 324 137 81 32 64 128 256), losses := [] }

theorem u2617 : Upper (D 3) (R 3) [6,40,320,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2618 : Route 9 := (fun mask => (mask,id))

def c2618 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2618 : Upper (D 3) (R 3) [6,40,320,129,96] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,96] 13 (by decide) (choices 1) [1,16,128] r2618 c2618
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u698
  · exact u699
  · exact u700

def b2619 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 324 137 145 113 113 241 369), lower := (rows 7 42 324 137 145 32 64 128 256), losses := [] }

theorem u2619 : Upper (D 3) (R 3) [6,40,320,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2619
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2620 : Route 9 := (fun mask => (mask,id))

def c2620 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2620 : Upper (D 3) (R 3) [6,40,320,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,160] 13 (by decide) (choices 1) [1,16,64] r2620 c2620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u701
  · exact u702
  · exact u703

def r2621 : Route 9 := (fun mask => (mask,id))

def c2621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2621 : Upper (D 3) (R 3) [6,40,320,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,320,129,192] 13 (by decide) (choices 1) [1,16] r2621 c2621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u704
  · exact u705

def b2622 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 152 49 225 193 193 449), lower := (rows 7 42 324 152 49 32 64 128 256), losses := [] }

theorem u2622 : Upper (D 3) (R 3) [6,40,320,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2623 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 324 152 81 161 225 161 417), lower := (rows 7 42 324 152 81 32 64 128 256), losses := [] }

theorem u2623 : Upper (D 3) (R 3) [6,40,320,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2624 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 453, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 324 152 112 161 193 129 385), lower := (rows 7 42 324 152 112 32 64 128 256), losses := [] }

theorem u2624 : Upper (D 3) (R 3) [6,40,320,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2625 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 145 97 97 225 353), lower := (rows 7 42 324 152 145 32 64 128 256), losses := [] }

theorem u2625 : Upper (D 3) (R 3) [6,40,320,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2626 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 324 152 176 97 65 193 321), lower := (rows 7 42 324 152 176 32 64 128 256), losses := [] }

theorem u2626 : Upper (D 3) (R 3) [6,40,320,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2627 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 324 152 208 33 97 161 289), lower := (rows 7 42 324 152 208 32 64 128 256), losses := [] }

theorem u2627 : Upper (D 3) (R 3) [6,40,320,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2628 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 261 25 25 224 224 224 480), lower := (rows 7 98 261 25 25 32 64 128 256), losses := [] }

theorem u2628 : Upper (D 3) (R 3) [6,96,257,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2629 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 25 49 232 200 200 456), lower := (rows 7 98 261 25 49 32 64 128 256), losses := [] }

theorem u2629 : Upper (D 3) (R 3) [6,96,257,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2630 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 261 25 56 225 193 193 449), lower := (rows 7 98 261 25 56 32 64 128 256), losses := [] }

theorem u2630 : Upper (D 3) (R 3) [6,96,257,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2631 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 261 25 112 169 201 137 393), lower := (rows 7 98 261 25 112 32 64 128 256), losses := [] }

theorem u2631 : Upper (D 3) (R 3) [6,96,257,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2632 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 261 25 145 232 232 232 488), lower := (rows 7 98 261 25 145 32 64 128 256), losses := [] }

theorem u2632 : Upper (D 3) (R 3) [6,96,257,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2633 : Route 9 := (fun mask => (mask,id))

def c2633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2633 : Upper (D 3) (R 3) [6,96,257,17,136] 13 := by
  apply FastRouting.sound _ _ [6,96,257,17,136] 13 (by decide) (choices 1) [1,64,128] r2633 c2633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u706
  · exact u707
  · exact u708

def b2634 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 25 176 233 201 201 457), lower := (rows 7 98 261 25 176 32 64 128 256), losses := [] }

theorem u2634 : Upper (D 3) (R 3) [6,96,257,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2635 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 41 88 177 209 145 401), lower := (rows 7 98 261 41 88 32 64 128 256), losses := [] }

theorem u2635 : Upper (D 3) (R 3) [6,96,257,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2636 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 41 145 248 216 216 472), lower := (rows 7 98 261 41 145 32 64 128 256), losses := [] }

theorem u2636 : Upper (D 3) (R 3) [6,96,257,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2637 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 41 152 241 209 209 465), lower := (rows 7 98 261 41 152 32 64 128 256), losses := [] }

theorem u2637 : Upper (D 3) (R 3) [6,96,257,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2638 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 261 41 208 185 217 153 409), lower := (rows 7 98 261 41 208 32 64 128 256), losses := [] }

theorem u2638 : Upper (D 3) (R 3) [6,96,257,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2639 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 56 88 161 193 129 385), lower := (rows 7 98 261 56 88 32 64 128 256), losses := [] }

theorem u2639 : Upper (D 3) (R 3) [6,96,257,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2639
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2639
end Delivery.IrregularNine14.P03
