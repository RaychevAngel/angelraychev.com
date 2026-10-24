import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0011
import IrregularNine14P03C0012

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2640 : Route 9 := (fun mask => (mask,id))

def c2640 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2640 : Upper (D 3) (R 3) [6,96,257,48,129] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,129] 13 (by decide) (choices 1) [1,8,64,128] r2640 c2640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u709
  · exact u710
  · exact u711
  · exact u712

def b2641 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 261 56 152 225 193 193 449), lower := (rows 7 98 261 56 152 32 64 128 256), losses := [] }

theorem u2641 : Upper (D 3) (R 3) [6,96,257,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2642 : Route 9 := (fun mask => (mask,id))

def c2642 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2642 : Upper (D 3) (R 3) [6,96,257,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,48,192] 13 (by decide) (choices 1) [1,8,128] r2642 c2642
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u713
  · exact u714
  · exact u715

def b2643 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 145 185 217 153 409), lower := (rows 7 98 261 104 145 32 64 128 256), losses := [] }

theorem u2643 : Upper (D 3) (R 3) [6,96,257,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2644 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 104 152 177 209 145 401), lower := (rows 7 98 261 104 152 32 64 128 256), losses := [] }

theorem u2644 : Upper (D 3) (R 3) [6,96,257,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2645 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 261 137 145 120 120 248 376), lower := (rows 7 98 261 137 145 32 64 128 256), losses := [] }

theorem u2645 : Upper (D 3) (R 3) [6,96,257,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2646 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 261 137 152 113 113 241 369), lower := (rows 7 98 261 137 152 32 64 128 256), losses := [] }

theorem u2646 : Upper (D 3) (R 3) [6,96,257,129,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2646
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2647 : Route 9 := (fun mask => (mask,id))

def c2647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2647 : Upper (D 3) (R 3) [6,96,257,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,257,129,160] 13 (by decide) (choices 1) [1,8,16,64] r2647 c2647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u716
  · exact u717
  · exact u718
  · exact u719

def b2648 : PairBound 9 := { available := 97, camps := [{ cop := 7, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 261 152 152 97 97 225 353), lower := (rows 7 98 261 152 152 32 64 128 256), losses := [] }

theorem u2648 : Upper (D 3) (R 3) [6,96,257,144,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2648
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2649 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 261 152 176 105 73 201 329), lower := (rows 7 98 261 152 176 32 64 128 256), losses := [] }

theorem u2649 : Upper (D 3) (R 3) [6,96,257,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2650 : Route 9 := (fun mask => (mask,id))

def c2650 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2650 : Upper (D 3) (R 3) [6,96,257,160,192] 13 := by
  apply FastRouting.sound _ _ [6,96,257,160,192] 13 (by decide) (choices 1) [1,8,16] r2650 c2650
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u720
  · exact u721
  · exact u722

def b2651 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 268 25 49 225 193 193 449), lower := (rows 7 98 268 25 49 32 64 128 256), losses := [] }

theorem u2651 : Upper (D 3) (R 3) [6,96,264,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2652 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 25 112 161 193 129 385), lower := (rows 7 98 268 25 112 32 64 128 256), losses := [] }

theorem u2652 : Upper (D 3) (R 3) [6,96,264,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2652
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2653 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 268 25 145 225 225 225 481), lower := (rows 7 98 268 25 145 32 64 128 256), losses := [] }

theorem u2653 : Upper (D 3) (R 3) [6,96,264,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2654 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 268 25 176 225 193 193 449), lower := (rows 7 98 268 25 176 32 64 128 256), losses := [] }

theorem u2654 : Upper (D 3) (R 3) [6,96,264,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2655 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 268 137 49 241 209 209 465), lower := (rows 7 98 268 137 49 32 64 128 256), losses := [] }

theorem u2655 : Upper (D 3) (R 3) [6,96,264,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2656 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 137 112 177 209 145 401), lower := (rows 7 98 268 137 112 32 64 128 256), losses := [] }

theorem u2656 : Upper (D 3) (R 3) [6,96,264,129,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2657 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 98 268 137 145 113 113 241 369), lower := (rows 7 98 268 137 145 32 64 128 256), losses := [] }

theorem u2657 : Upper (D 3) (R 3) [6,96,264,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2657
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2658 : Route 9 := (fun mask => (mask,id))

def c2658 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2658 : Upper (D 3) (R 3) [6,96,264,129,160] 13 := by
  apply FastRouting.sound _ _ [6,96,264,129,160] 13 (by decide) (choices 1) [1,16,64] r2658 c2658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u723
  · exact u724
  · exact u725

def b2659 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 268 152 49 225 193 193 449), lower := (rows 7 98 268 152 49 32 64 128 256), losses := [] }

theorem u2659 : Upper (D 3) (R 3) [6,96,264,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2659
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2660 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 268 152 112 161 193 129 385), lower := (rows 7 98 268 152 112 32 64 128 256), losses := [] }

theorem u2660 : Upper (D 3) (R 3) [6,96,264,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2661 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 152 145 97 97 225 353), lower := (rows 7 98 268 152 145 32 64 128 256), losses := [] }

theorem u2661 : Upper (D 3) (R 3) [6,96,264,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2661
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2662 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 268 152 176 97 65 193 321), lower := (rows 7 98 268 152 176 32 64 128 256), losses := [] }

theorem u2662 : Upper (D 3) (R 3) [6,96,264,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2662
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2663 : PairBound 9 := { available := 225, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 388 25 25 225 225 225 481), lower := (rows 7 98 388 25 25 32 64 128 256), losses := [] }

theorem u2663 : Upper (D 3) (R 3) [6,96,384,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2664 : PairBound 9 := { available := 201, camps := [{ cop := 4, region := 460, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 25 49 233 201 201 457), lower := (rows 7 98 388 25 49 32 64 128 256), losses := [] }

theorem u2664 : Upper (D 3) (R 3) [6,96,384,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2664
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2665 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 388 25 56 225 193 193 449), lower := (rows 7 98 388 25 56 32 64 128 256), losses := [] }

theorem u2665 : Upper (D 3) (R 3) [6,96,384,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2666 : PairBound 9 := { available := 137, camps := [{ cop := 1, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 98 388 25 112 169 201 137 393), lower := (rows 7 98 388 25 112 32 64 128 256), losses := [] }

theorem u2666 : Upper (D 3) (R 3) [6,96,384,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2666
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2667 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 388 25 145 105 105 233 361), lower := (rows 7 98 388 25 145 32 64 128 256), losses := [] }

theorem u2667 : Upper (D 3) (R 3) [6,96,384,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2667
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2668 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 388 25 152 97 97 225 353), lower := (rows 7 98 388 25 152 32 64 128 256), losses := [] }

theorem u2668 : Upper (D 3) (R 3) [6,96,384,17,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2668
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2669 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 452, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 25 176 105 73 201 329), lower := (rows 7 98 388 25 176 32 64 128 256), losses := [] }

theorem u2669 : Upper (D 3) (R 3) [6,96,384,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2669
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2670 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 41 88 177 209 145 401), lower := (rows 7 98 388 41 88 32 64 128 256), losses := [] }

theorem u2670 : Upper (D 3) (R 3) [6,96,384,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2671 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 41 152 113 81 209 337), lower := (rows 7 98 388 41 152 32 64 128 256), losses := [] }

theorem u2671 : Upper (D 3) (R 3) [6,96,384,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2671
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2672 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 468, targets := 32 }], pairs := [(2,5)], upper := (rows 7 98 388 41 208 57 89 153 281), lower := (rows 7 98 388 41 208 32 64 128 256), losses := [] }

theorem u2672 : Upper (D 3) (R 3) [6,96,384,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2673 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 56 88 161 193 129 385), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u2673 : Upper (D 3) (R 3) [6,96,384,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2674 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 56 145 105 73 201 329), lower := (rows 7 98 388 56 145 32 64 128 256), losses := [] }

theorem u2674 : Upper (D 3) (R 3) [6,96,384,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2675 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 98 388 56 152 97 65 193 321), lower := (rows 7 98 388 56 152 32 64 128 256), losses := [] }

theorem u2675 : Upper (D 3) (R 3) [6,96,384,48,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2676 : Route 9 := (fun mask => (mask,id))

def c2676 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2676 : Upper (D 3) (R 3) [6,96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192] 13 (by decide) (choices 1) [1,8] r2676 c2676
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u726
  · exact u727

def b2677 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 104 152 49 81 145 273), lower := (rows 7 98 388 104 152 32 64 128 256), losses := [] }

theorem u2677 : Upper (D 3) (R 3) [6,96,384,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2678 : PairBound 9 := { available := 448, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 41 81 480 448 448 448), lower := (rows 35 7 28 41 81 32 64 128 256), losses := [] }

theorem u2678 : Upper (D 3) (R 3) [34,5,24,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2678
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2679 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 41 208 481 449 449 449), lower := (rows 35 7 28 41 208 32 64 128 256), losses := [] }

theorem u2679 : Upper (D 3) (R 3) [34,5,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2679
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2680 : PairBound 9 := { available := 192, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 41 273 224 192 192 448), lower := (rows 35 7 28 41 273 32 64 128 256), losses := [] }

theorem u2680 : Upper (D 3) (R 3) [34,5,24,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2680
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2681 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 41 336 225 193 193 449), lower := (rows 35 7 28 41 336 32 64 128 256), losses := [] }

theorem u2681 : Upper (D 3) (R 3) [34,5,24,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2681
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2682 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 22, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 28 73 81 416 480 416 416), lower := (rows 35 7 28 73 81 32 64 128 256), losses := [] }

theorem u2682 : Upper (D 3) (R 3) [34,5,24,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2682
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2683 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 15, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 28 73 112 417 449 385 385), lower := (rows 35 7 28 73 112 32 64 128 256), losses := [] }

theorem u2683 : Upper (D 3) (R 3) [34,5,24,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2683
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m2684_128 : Upper (D 3) (R 3) [34,5,24,65,129,128] 13 :=
  permutation_upper _ _ _ [34,5,24,65,129,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u728

def r2684 : Route 9 := (fun mask => (mask,id))

def c2684 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u2684 : Upper (D 3) (R 3) [34,5,24,65,129] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,129] 13 (by decide) (choices 1) [64,128,256] r2684 c2684
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u728
  · exact m2684_128
  · exact u729

def b2685 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 28 73 176 481 449 449 449), lower := (rows 35 7 28 73 176 32 64 128 256), losses := [] }

theorem u2685 : Upper (D 3) (R 3) [34,5,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2685
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2686 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 73 208 417 481 417 417), lower := (rows 35 7 28 73 208 32 64 128 256), losses := [] }

theorem u2686 : Upper (D 3) (R 3) [34,5,24,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2686
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2687 : Route 9 := (fun mask => (mask,id))

def c2687 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2687 : Upper (D 3) (R 3) [34,5,24,65,257] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,257] 13 (by decide) (choices 1) [64,128] r2687 c2687
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u730
  · exact u731

def b2688 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 28 73 304 225 193 193 449), lower := (rows 35 7 28 73 304 32 64 128 256), losses := [] }

theorem u2688 : Upper (D 3) (R 3) [34,5,24,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2688
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2689 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 73 336 161 225 161 417), lower := (rows 35 7 28 73 336 32 64 128 256), losses := [] }

theorem u2689 : Upper (D 3) (R 3) [34,5,24,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2689
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2690 : Route 9 := (fun mask => (mask,id))

def c2690 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2690 : Upper (D 3) (R 3) [34,5,24,65,384] 13 := by
  apply FastRouting.sound _ _ [34,5,24,65,384] 13 (by decide) (choices 1) [1,64,128] r2690 c2690
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u732
  · exact u733
  · exact u734

def b2691 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 208 417 449 385 385), lower := (rows 35 7 28 104 208 32 64 128 256), losses := [] }

theorem u2691 : Upper (D 3) (R 3) [34,5,24,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2691
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2692 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 28 104 273 225 193 193 449), lower := (rows 35 7 28 104 273 32 64 128 256), losses := [] }

theorem u2692 : Upper (D 3) (R 3) [34,5,24,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2692
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2693 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 336 161 193 129 385), lower := (rows 35 7 28 104 336 32 64 128 256), losses := [] }

theorem u2693 : Upper (D 3) (R 3) [34,5,24,96,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2693
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2694 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 28 104 400 225 193 193 449), lower := (rows 35 7 28 104 400 32 64 128 256), losses := [] }

theorem u2694 : Upper (D 3) (R 3) [34,5,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2694
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2695 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 28 200 208 289 353 417 289), lower := (rows 35 7 28 200 208 32 64 128 256), losses := [] }

theorem u2695 : Upper (D 3) (R 3) [34,5,24,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2695
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2696 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2696 : Upper (D 3) (R 3) [34,5,24,192,257] 13 := by
  apply FastRouting.sound _ _ [34,5,24,192,257] 13 (by decide) (choices 1) [1,64] r2696 c2696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u735
  · exact u736

def b2697 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 28 200 304 225 193 193 449), lower := (rows 35 7 28 200 304 32 64 128 256), losses := [] }

theorem u2697 : Upper (D 3) (R 3) [34,5,24,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2697
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2698 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 200 336 161 225 161 417), lower := (rows 35 7 28 200 336 32 64 128 256), losses := [] }

theorem u2698 : Upper (D 3) (R 3) [34,5,24,192,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2698
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2699 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 25 49 480 448 448 448), lower := (rows 35 7 76 25 49 32 64 128 256), losses := [] }

theorem u2699 : Upper (D 3) (R 3) [34,5,72,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2699
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2699
end Delivery.IrregularNine14.P03
