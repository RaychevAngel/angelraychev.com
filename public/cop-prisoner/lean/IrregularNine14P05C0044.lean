import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0009
import IrregularNine14P05C0010

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2640 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 325, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 69 168 28 40 323 387 259), lower := (rows 7 50 69 168 28 40 64 128 256), losses := [] }

theorem u2640 : Upper (D 5) (R 5) [6,48,65,160,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2640
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2641 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 424, targets := 4 }], pairs := [(3,2)], upper := (rows 7 50 69 168 28 288 75 139 267), lower := (rows 7 50 69 168 28 288 64 128 256), losses := [] }

theorem u2641 : Upper (D 5) (R 5) [6,48,65,160,12,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2641
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2642 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 136, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 50 69 168 276 33 74 138 266), lower := (rows 7 50 69 168 276 33 64 128 256), losses := [] }

theorem u2642 : Upper (D 5) (R 5) [6,48,65,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2642
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2643 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 276 34 73 137 265), lower := (rows 7 50 69 168 276 34 64 128 256), losses := [] }

theorem u2643 : Upper (D 5) (R 5) [6,48,65,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2643
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 11, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 50 69 168 276 40 75 139 267), lower := (rows 7 50 69 168 276 40 64 128 256), losses := [] }

theorem u2644 : Upper (D 5) (R 5) [6,48,65,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2644
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2645 : Route 9 := (fun mask => (mask,id))

def c2645 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2645 : Upper (D 5) (R 5) [6,48,65,160,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160,264,1] 13 (by decide) (choices 1) [2,4,8] r2645 c2645
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u566
  · exact u567
  · exact u568

def b2646 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 168 280 34 77 141 269), lower := (rows 7 50 69 168 280 34 64 128 256), losses := [] }

theorem u2646 : Upper (D 5) (R 5) [6,48,65,160,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2646
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2647 : Route 9 := (fun mask => (mask,id))

def c2647 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2647 : Upper (D 5) (R 5) [6,48,65,160,264,4] 13 := by
  apply FastRouting.sound _ _ [6,48,65,160,264,4] 13 (by decide) (choices 1) [1,2,8] r2647 c2647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u569
  · exact u570
  · exact u571

def b2648 : PairBound 9 := { available := 7, camps := [{ cop := 1, region := 69, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 50 69 168 280 40 71 135 263), lower := (rows 7 50 69 168 280 40 64 128 256), losses := [] }

theorem u2648 : Upper (D 5) (R 5) [6,48,65,160,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2648
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 392, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 50 69 392 28 33 106 170 298), lower := (rows 7 50 69 392 28 33 64 128 256), losses := [] }

theorem u2649 : Upper (D 5) (R 5) [6,48,65,384,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2649
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2650 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 69 392 28 34 105 169 297), lower := (rows 7 50 69 392 28 34 64 128 256), losses := [] }

theorem u2650 : Upper (D 5) (R 5) [6,48,65,384,12,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2650
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2651 : PairBound 9 := { available := 35, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3),(2,3)], upper := (rows 7 50 69 392 28 40 99 163 291), lower := (rows 7 50 69 392 28 40 64 128 256), losses := [] }

theorem u2651 : Upper (D 5) (R 5) [6,48,65,384,12,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2651
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 76 41 145 34 332 396 268), lower := (rows 7 50 76 41 145 34 64 128 256), losses := [] }

theorem u2652 : Upper (D 5) (R 5) [6,48,72,33,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2652
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 50 76 41 145 36 330 394 266), lower := (rows 7 50 76 41 145 36 64 128 256), losses := [] }

theorem u2653 : Upper (D 5) (R 5) [6,48,72,33,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2653
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 50 76 41 145 40 326 390 262), lower := (rows 7 50 76 41 145 40 64 128 256), losses := [] }

theorem u2654 : Upper (D 5) (R 5) [6,48,72,33,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2654
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2655 : Route 9 := (fun mask => (mask,id))

def c2655 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2655 : Upper (D 5) (R 5) [6,48,72,33,129,256] 13 := by
  apply FastRouting.sound _ _ [6,48,72,33,129,256] 13 (by decide) (choices 1) [2,4,8] r2655 c2655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u572
  · exact u573
  · exact u574

def b2656 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 50 76 41 148 33 330 394 266), lower := (rows 7 50 76 41 148 33 64 128 256), losses := [] }

theorem u2656 : Upper (D 5) (R 5) [6,48,72,33,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2656
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 265, camps := [{ cop := 3, region := 324, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 76 41 148 34 329 393 265), lower := (rows 7 50 76 41 148 34 64 128 256), losses := [] }

theorem u2657 : Upper (D 5) (R 5) [6,48,72,33,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2657
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2658 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 400, targets := 40 }], pairs := [(4,3),(4,5)], upper := (rows 7 50 76 41 148 40 323 387 259), lower := (rows 7 50 76 41 148 40 64 128 256), losses := [] }

theorem u2658 : Upper (D 5) (R 5) [6,48,72,33,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2658
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2659 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 296, targets := 4 }], pairs := [(3,2)], upper := (rows 7 50 76 41 148 288 75 139 267), lower := (rows 7 50 76 41 148 288 64 128 256), losses := [] }

theorem u2659 : Upper (D 5) (R 5) [6,48,72,33,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2659
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 14, camps := [{ cop := 3, region := 470, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 50 76 41 400 33 78 142 270), lower := (rows 7 50 76 41 400 33 64 128 256), losses := [] }

theorem u2660 : Upper (D 5) (R 5) [6,48,72,33,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2660
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 13, camps := [{ cop := 3, region := 68, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 50 76 41 400 34 77 141 269), lower := (rows 7 50 76 41 400 34 64 128 256), losses := [] }

theorem u2661 : Upper (D 5) (R 5) [6,48,72,33,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2661
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 11, camps := [{ cop := 3, region := 402, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 50 76 41 400 36 75 139 267), lower := (rows 7 50 76 41 400 36 64 128 256), losses := [] }

theorem u2662 : Upper (D 5) (R 5) [6,48,72,33,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2662
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 50 76 41 400 40 71 135 263), lower := (rows 7 50 76 41 400 40 64 128 256), losses := [] }

theorem u2663 : Upper (D 5) (R 5) [6,48,72,33,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2663
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 332, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 76 44 145 33 330 394 266), lower := (rows 7 50 76 44 145 33 64 128 256), losses := [] }

theorem u2664 : Upper (D 5) (R 5) [6,48,72,36,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2664
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 265, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 145 34 329 393 265), lower := (rows 7 50 76 44 145 34 64 128 256), losses := [] }

theorem u2665 : Upper (D 5) (R 5) [6,48,72,36,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2665
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 50 76 44 145 40 323 387 259), lower := (rows 7 50 76 44 145 40 64 128 256), losses := [] }

theorem u2666 : Upper (D 5) (R 5) [6,48,72,36,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2666
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2667 : Route 9 := (fun mask => (mask,id))

def c2667 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2667 : Upper (D 5) (R 5) [6,48,72,36,129,256] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,129,256] 13 (by decide) (choices 1) [1,2,8] r2667 c2667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u575
  · exact u576
  · exact u577

def r2668 : Route 9 := (fun mask => (mask,id))

def c2668 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | _ => 0)

theorem u2668 : Upper (D 5) (R 5) [6,48,72,36,136,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,136,1] 13 (by decide) (choices 1) [1,2,256] r2668 c2668
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u578
  · exact u579
  · exact u580

def b2669 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 152 34 321 385 257), lower := (rows 7 50 76 44 152 34 64 128 256), losses := [] }

theorem u2669 : Upper (D 5) (R 5) [6,48,72,36,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2669
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2670 : Route 9 := (fun mask => (mask,id))

def c2670 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2670 : Upper (D 5) (R 5) [6,48,72,36,136,256] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,136,256] 13 (by decide) (choices 1) [1,2] r2670 c2670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u581
  · exact u582

def r2671 : Route 9 := (fun mask => (mask,id))

def c2671 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2671 : Upper (D 5) (R 5) [6,48,72,36,384,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,36,384,1] 13 (by decide) (choices 1) [1,2,8] r2671 c2671
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u583
  · exact u584
  · exact u585

def b2672 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 44 400 34 73 137 265), lower := (rows 7 50 76 44 400 34 64 128 256), losses := [] }

theorem u2672 : Upper (D 5) (R 5) [6,48,72,36,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2672
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 50 76 44 400 40 67 131 259), lower := (rows 7 50 76 44 400 40 64 128 256), losses := [] }

theorem u2673 : Upper (D 5) (R 5) [6,48,72,36,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2673
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 44, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 137 273 34 108 172 300), lower := (rows 7 50 76 137 273 34 64 128 256), losses := [] }

theorem u2674 : Upper (D 5) (R 5) [6,48,72,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2674
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 42, camps := [], pairs := [(1,0),(1,3)], upper := (rows 7 50 76 137 273 36 106 170 298), lower := (rows 7 50 76 137 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 108 168 306 36 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 37 64 128 256), good := (rows 39 50 100 161 307 36 64 128 256) }] }

theorem u2675 : Upper (D 5) (R 5) [6,48,72,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2675
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2676 : Route 9 := (fun mask => (mask,id))

def c2676 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2676 : Upper (D 5) (R 5) [6,48,72,129,257,8] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129,257,8] 13 (by decide) (choices 1) [2,4,32] r2676 c2676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u586
  · exact u587
  · exact u588

def b2677 : PairBound 9 := { available := 42, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 76 137 276 33 106 170 298), lower := (rows 7 50 76 137 276 33 64 128 256), losses := [] }

theorem u2677 : Upper (D 5) (R 5) [6,48,72,129,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2677
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 137 276 34 105 169 297), lower := (rows 7 50 76 137 276 34 64 128 256), losses := [] }

theorem u2678 : Upper (D 5) (R 5) [6,48,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2678
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 50 76 137 276 40 99 163 291), lower := (rows 7 50 76 137 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 44 64 128 256), good := (rows 38 50 108 168 310 40 64 128 256) }] }

theorem u2679 : Upper (D 5) (R 5) [6,48,72,129,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2679
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 38, camps := [], pairs := [(1,2),(1,3)], upper := (rows 7 50 76 137 280 33 102 166 294), lower := (rows 7 50 76 137 280 33 64 128 256), losses := [{ target := 2, region := (rows 1 18 0 8 16 41 64 128 256), good := (rows 35 50 104 169 314 33 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 41 65 129 257), good := (rows 487 50 100 481 306 481 64 128 256) }] }

theorem u2680 : Upper (D 5) (R 5) [6,48,72,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2680
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 137 280 34 101 165 293), lower := (rows 7 50 76 137 280 34 64 128 256), losses := [] }

theorem u2681 : Upper (D 5) (R 5) [6,48,72,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2681
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2682 : Route 9 := (fun mask => (mask,id))

def c2682 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2682 : Upper (D 5) (R 5) [6,48,72,129,264,4] 13 := by
  apply FastRouting.sound _ _ [6,48,72,129,264,4] 13 (by decide) (choices 1) [1,2,32] r2682 c2682
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u589
  · exact u590
  · exact u591

def b2683 : PairBound 9 := { available := 44, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 76 138 273 33 108 172 300), lower := (rows 7 50 76 138 273 33 64 128 256), losses := [] }

theorem u2683 : Upper (D 5) (R 5) [6,48,72,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2683
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2684 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0),(1,3)], upper := (rows 7 50 76 138 273 36 105 169 297), lower := (rows 7 50 76 138 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 108 138 306 36 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 37 64 128 256), good := (rows 39 50 100 130 307 36 64 128 256) }] }

theorem u2684 : Upper (D 5) (R 5) [6,48,72,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2684
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2685 : Route 9 := (fun mask => (mask,id))

def c2685 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2685 : Upper (D 5) (R 5) [6,48,72,130,257,8] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,257,8] 13 (by decide) (choices 1) [1,4,32] r2685 c2685
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u592
  · exact u593
  · exact u594

def b2686 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 76 138 276 33 105 169 297), lower := (rows 7 50 76 138 276 33 64 128 256), losses := [] }

theorem u2686 : Upper (D 5) (R 5) [6,48,72,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2686
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2687 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 4 }], pairs := [(1,0),(3,2)], upper := (rows 7 50 76 138 276 40 97 161 289), lower := (rows 7 50 76 138 276 40 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 44 64 128 256), good := (rows 38 50 108 170 310 40 64 128 256) }] }

theorem u2687 : Upper (D 5) (R 5) [6,48,72,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2687
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2688 : Route 9 := (fun mask => (mask,id))

def c2688 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2688 : Upper (D 5) (R 5) [6,48,72,130,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,264,1] 13 (by decide) (choices 1) [1,4,32] r2688 c2688
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u595
  · exact u596
  · exact u597

def r2689 : Route 9 := (fun mask => (mask,id))

def c2689 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2689 : Upper (D 5) (R 5) [6,48,72,130,264,4] 13 := by
  apply FastRouting.sound _ _ [6,48,72,130,264,4] 13 (by decide) (choices 1) [1,32] r2689 c2689
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u598
  · exact u599

def b2690 : PairBound 9 := { available := 42, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 76 140 273 33 106 170 298), lower := (rows 7 50 76 140 273 33 64 128 256), losses := [] }

theorem u2690 : Upper (D 5) (R 5) [6,48,72,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2690
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2691 : PairBound 9 := { available := 41, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 140 273 34 105 169 297), lower := (rows 7 50 76 140 273 34 64 128 256), losses := [] }

theorem u2691 : Upper (D 5) (R 5) [6,48,72,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2691
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 50 76 140 273 40 99 163 291), lower := (rows 7 50 76 140 273 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 17 44 65 129 257), good := (rows 499 50 104 168 467 40 64 128 256) }] }

theorem u2692 : Upper (D 5) (R 5) [6,48,72,132,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2692
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2693 : Route 9 := (fun mask => (mask,id))

def c2693 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2693 : Upper (D 5) (R 5) [6,48,72,132,264,1] 13 := by
  apply FastRouting.sound _ _ [6,48,72,132,264,1] 13 (by decide) (choices 1) [1,2,32] r2693 c2693
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u600
  · exact u601
  · exact u602

def b2694 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 140 280 34 97 161 289), lower := (rows 7 50 76 140 280 34 64 128 256), losses := [] }

theorem u2694 : Upper (D 5) (R 5) [6,48,72,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2694
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 50 76 168 273 33 78 142 270), lower := (rows 7 50 76 168 273 33 64 128 256), losses := [] }

theorem u2695 : Upper (D 5) (R 5) [6,48,72,160,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2695
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2696 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 34, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 50 76 168 273 34 77 141 269), lower := (rows 7 50 76 168 273 34 64 128 256), losses := [] }

theorem u2696 : Upper (D 5) (R 5) [6,48,72,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2696
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2697 : PairBound 9 := { available := 11, camps := [], pairs := [(1,0),(1,3)], upper := (rows 7 50 76 168 273 36 75 139 267), lower := (rows 7 50 76 168 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 16 37 64 128 256), good := (rows 38 50 108 168 306 36 64 128 256) },{ target := 3, region := (rows 1 18 4 0 16 37 64 128 256), good := (rows 39 50 100 160 307 36 64 128 256) }] }

theorem u2697 : Upper (D 5) (R 5) [6,48,72,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2697
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 7, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 50 76 168 273 40 71 135 263), lower := (rows 7 50 76 168 273 40 64 128 256), losses := [] }

theorem u2698 : Upper (D 5) (R 5) [6,48,72,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2698
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 11, camps := [{ cop := 4, region := 35, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 50 76 168 276 33 75 139 267), lower := (rows 7 50 76 168 276 33 64 128 256), losses := [] }

theorem u2699 : Upper (D 5) (R 5) [6,48,72,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2699
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P05
