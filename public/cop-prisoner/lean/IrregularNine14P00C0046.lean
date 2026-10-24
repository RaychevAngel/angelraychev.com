import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0026

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2760 : Route 9 := (fun mask => (mask,id))

def c2760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2760 : Upper (D 0) (R 0) [50,320,129,192] 13 := by
  apply FastRouting.sound _ _ [50,320,129,192] 13 (by decide) (choices 1) [1,4,8,32] r2760 c2760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1589
  · exact u1590
  · exact u1591
  · exact u1592

def b2761 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 140 140 113 113 113 241 369), lower := (rows 51 322 140 140 16 32 64 128 256), losses := [] }

theorem u2761 : Upper (D 0) (R 0) [50,320,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2761
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 140 152 117 101 101 229 357), lower := (rows 51 322 140 152 16 32 64 128 256), losses := [] }

theorem u2762 : Upper (D 0) (R 0) [50,320,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2762
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 140 200 53 53 117 181 309), lower := (rows 51 322 140 200 16 32 64 128 256), losses := [] }

theorem u2763 : Upper (D 0) (R 0) [50,320,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2763
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2764 : Route 9 := (fun mask => (mask,id))

def c2764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2764 : Upper (D 0) (R 0) [50,320,144,160] 13 := by
  apply FastRouting.sound _ _ [50,320,144,160] 13 (by decide) (choices 1) [1,4,8,64] r2764 c2764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1593
  · exact u1594
  · exact u1595
  · exact u1596

def r2765 : Route 9 := (fun mask => (mask,id))

def c2765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2765 : Upper (D 0) (R 0) [50,320,144,192] 13 := by
  apply FastRouting.sound _ _ [50,320,144,192] 13 (by decide) (choices 1) [1,4,8,32] r2765 c2765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1597
  · exact u1598
  · exact u1599
  · exact u1600

def b2766 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 7 152 504 488 488 488 488), lower := (rows 113 7 7 152 16 32 64 128 256), losses := [] }

theorem u2766 : Upper (D 0) (R 0) [112,5,3,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2766
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 7 280 248 232 232 232 488), lower := (rows 113 7 7 280 16 32 64 128 256), losses := [] }

theorem u2767 : Upper (D 0) (R 0) [112,5,3,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2767
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2768 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 7 392 248 248 248 248 504), lower := (rows 113 7 7 392 16 32 64 128 256), losses := [] }

theorem u2768 : Upper (D 0) (R 0) [112,5,3,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2768
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 13 26 496 480 480 480 480), lower := (rows 113 7 13 26 16 32 64 128 256), losses := [] }

theorem u2769 : Upper (D 0) (R 0) [112,5,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2769
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 13 138 496 496 496 496 496), lower := (rows 113 7 13 138 16 32 64 128 256), losses := [] }

theorem u2770 : Upper (D 0) (R 0) [112,5,9,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2770
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 482, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 13 152 498 482 482 482 482), lower := (rows 113 7 13 152 16 32 64 128 256), losses := [] }

theorem u2771 : Upper (D 0) (R 0) [112,5,9,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2771
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 13 266 240 240 240 240 496), lower := (rows 113 7 13 266 16 32 64 128 256), losses := [] }

theorem u2772 : Upper (D 0) (R 0) [112,5,9,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2772
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 226, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 13 280 242 226 226 226 482), lower := (rows 113 7 13 280 16 32 64 128 256), losses := [] }

theorem u2773 : Upper (D 0) (R 0) [112,5,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2773
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 13 392 242 242 242 242 498), lower := (rows 113 7 13 392 16 32 64 128 256), losses := [] }

theorem u2774 : Upper (D 0) (R 0) [112,5,9,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2774
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 25 496 480 480 480 480), lower := (rows 113 7 14 25 16 32 64 128 256), losses := [] }

theorem u2775 : Upper (D 0) (R 0) [112,5,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2775
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2776 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 14 56 465 481 449 449 449), lower := (rows 113 7 14 56 16 32 64 128 256), losses := [] }

theorem u2776 : Upper (D 0) (R 0) [112,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2776
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2777 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 14 137 496 496 496 496 496), lower := (rows 113 7 14 137 16 32 64 128 256), losses := [] }

theorem u2777 : Upper (D 0) (R 0) [112,5,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2777
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2778 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u2778 : Upper (D 0) (R 0) [112,5,10,144] 13 := by
  apply FastRouting.sound _ _ [112,5,10,144] 13 (by decide) (choices 1) [1,32,128,256] r2778 c2778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1601
  · exact u1602
  · exact u1603
  · exact u1604

def b2779 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 14 265 240 240 240 240 496), lower := (rows 113 7 14 265 16 32 64 128 256), losses := [] }

theorem u2779 : Upper (D 0) (R 0) [112,5,10,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2779
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2780 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2780 : Upper (D 0) (R 0) [112,5,10,272] 13 := by
  apply FastRouting.sound _ _ [112,5,10,272] 13 (by decide) (choices 1) [1,32,128] r2780 c2780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1605
  · exact u1606
  · exact u1607

def r2781 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2781 : Upper (D 0) (R 0) [112,5,10,384] 13 := by
  apply FastRouting.sound _ _ [112,5,10,384] 13 (by decide) (choices 1) [1,32,128] r2781 c2781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1608
  · exact u1609
  · exact u1610

def b2782 : PairBound 9 := { available := 456, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 21 42 472 488 456 456 456), lower := (rows 113 7 21 42 16 32 64 128 256), losses := [] }

theorem u2782 : Upper (D 0) (R 0) [112,5,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2782
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 21 138 504 488 488 488 488), lower := (rows 113 7 21 138 16 32 64 128 256), losses := [] }

theorem u2783 : Upper (D 0) (R 0) [112,5,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2783
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 21 168 474 490 458 458 458), lower := (rows 113 7 21 168 16 32 64 128 256), losses := [] }

theorem u2784 : Upper (D 0) (R 0) [112,5,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2784
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 21 266 248 232 232 232 488), lower := (rows 113 7 21 266 16 32 64 128 256), losses := [] }

theorem u2785 : Upper (D 0) (R 0) [112,5,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2785
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 21 296 218 234 202 202 458), lower := (rows 113 7 21 296 16 32 64 128 256), losses := [] }

theorem u2786 : Upper (D 0) (R 0) [112,5,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2786
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 21 392 250 234 234 234 490), lower := (rows 113 7 21 392 16 32 64 128 256), losses := [] }

theorem u2787 : Upper (D 0) (R 0) [112,5,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2787
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 137 504 488 488 488 488), lower := (rows 113 7 22 137 16 32 64 128 256), losses := [] }

theorem u2788 : Upper (D 0) (R 0) [112,5,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2788
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 168 473 489 457 457 457), lower := (rows 113 7 22 168 16 32 64 128 256), losses := [] }

theorem u2789 : Upper (D 0) (R 0) [112,5,18,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2789
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 265 248 232 232 232 488), lower := (rows 113 7 22 265 16 32 64 128 256), losses := [] }

theorem u2790 : Upper (D 0) (R 0) [112,5,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2790
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 296 217 233 201 201 457), lower := (rows 113 7 22 296 16 32 64 128 256), losses := [] }

theorem u2791 : Upper (D 0) (R 0) [112,5,18,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2791
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 22 392 249 233 233 233 489), lower := (rows 113 7 22 392 16 32 64 128 256), losses := [] }

theorem u2792 : Upper (D 0) (R 0) [112,5,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2792
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2793 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 28 42 465 481 449 449 449), lower := (rows 113 7 28 42 16 32 64 128 256), losses := [] }

theorem u2793 : Upper (D 0) (R 0) [112,5,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2793
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 137 498 482 482 482 482), lower := (rows 113 7 28 137 16 32 64 128 256), losses := [] }

theorem u2794 : Upper (D 0) (R 0) [112,5,24,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2794
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 481, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 138 497 481 481 481 481), lower := (rows 113 7 28 138 16 32 64 128 256), losses := [] }

theorem u2795 : Upper (D 0) (R 0) [112,5,24,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2795
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 168 467 483 451 451 451), lower := (rows 113 7 28 168 16 32 64 128 256), losses := [] }

theorem u2796 : Upper (D 0) (R 0) [112,5,24,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2796
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 265 242 226 226 226 482), lower := (rows 113 7 28 265 16 32 64 128 256), losses := [] }

theorem u2797 : Upper (D 0) (R 0) [112,5,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2797
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 266 241 225 225 225 481), lower := (rows 113 7 28 266 16 32 64 128 256), losses := [] }

theorem u2798 : Upper (D 0) (R 0) [112,5,24,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2798
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2799 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 296 211 227 195 195 451), lower := (rows 113 7 28 296 16 32 64 128 256), losses := [] }

theorem u2799 : Upper (D 0) (R 0) [112,5,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2799
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2800 : PairBound 9 := { available := 227, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 113 7 28 392 243 227 227 227 483), lower := (rows 113 7 28 392 16 32 64 128 256), losses := [] }

theorem u2800 : Upper (D 0) (R 0) [112,5,24,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2800
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 113 7 52 74 409 425 457 393 393), lower := (rows 113 7 52 74 16 32 64 128 256), losses := [] }

theorem u2801 : Upper (D 0) (R 0) [112,5,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2801
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 137 474 490 458 458 458), lower := (rows 113 7 52 137 16 32 64 128 256), losses := [] }

theorem u2802 : Upper (D 0) (R 0) [112,5,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2802
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2803 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 138 473 489 457 457 457), lower := (rows 113 7 52 138 16 32 64 128 256), losses := [] }

theorem u2803 : Upper (D 0) (R 0) [112,5,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2803
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2804 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 200 411 427 459 395 395), lower := (rows 113 7 52 200 16 32 64 128 256), losses := [] }

theorem u2804 : Upper (D 0) (R 0) [112,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2804
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 265 218 234 202 202 458), lower := (rows 113 7 52 265 16 32 64 128 256), losses := [] }

theorem u2805 : Upper (D 0) (R 0) [112,5,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2805
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 266 217 233 201 201 457), lower := (rows 113 7 52 266 16 32 64 128 256), losses := [] }

theorem u2806 : Upper (D 0) (R 0) [112,5,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2806
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 328 155 171 203 139 395), lower := (rows 113 7 52 328 16 32 64 128 256), losses := [] }

theorem u2807 : Upper (D 0) (R 0) [112,5,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2807
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 113 7 52 392 219 235 203 203 459), lower := (rows 113 7 52 392 16 32 64 128 256), losses := [] }

theorem u2808 : Upper (D 0) (R 0) [112,5,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2808
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 488, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 26 504 488 488 488 488), lower := (rows 113 7 133 26 16 32 64 128 256), losses := [] }

theorem u2809 : Upper (D 0) (R 0) [112,5,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2809
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 376, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 138 376 376 376 504 376), lower := (rows 113 7 133 138 16 32 64 128 256), losses := [] }

theorem u2810 : Upper (D 0) (R 0) [112,5,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2810
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 362, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 152 378 362 362 490 362), lower := (rows 113 7 133 152 16 32 64 128 256), losses := [] }

theorem u2811 : Upper (D 0) (R 0) [112,5,129,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2811
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 266 248 248 248 248 504), lower := (rows 113 7 133 266 16 32 64 128 256), losses := [] }

theorem u2812 : Upper (D 0) (R 0) [112,5,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2812
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2813 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 280 250 234 234 234 490), lower := (rows 113 7 133 280 16 32 64 128 256), losses := [] }

theorem u2813 : Upper (D 0) (R 0) [112,5,129,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2813
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2814 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 133 392 122 122 122 250 378), lower := (rows 113 7 133 392 16 32 64 128 256), losses := [] }

theorem u2814 : Upper (D 0) (R 0) [112,5,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2814
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2815 : PairBound 9 := { available := 488, camps := [{ cop := 0, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 134 25 504 488 488 488 488), lower := (rows 113 7 134 25 16 32 64 128 256), losses := [] }

theorem u2815 : Upper (D 0) (R 0) [112,5,130,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2815
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2816 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 113 7 134 56 473 489 457 457 457), lower := (rows 113 7 134 56 16 32 64 128 256), losses := [] }

theorem u2816 : Upper (D 0) (R 0) [112,5,130,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2816
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 376, camps := [{ cop := 3, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 113 7 134 137 376 376 376 504 376), lower := (rows 113 7 134 137 16 32 64 128 256), losses := [] }

theorem u2817 : Upper (D 0) (R 0) [112,5,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2817
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 134 152 377 361 361 489 361), lower := (rows 113 7 134 152 16 32 64 128 256), losses := [] }

theorem u2818 : Upper (D 0) (R 0) [112,5,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b2818
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r2819 : Route 9 := (fun mask => match mask with | 64 => (32,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c2819 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u2819 : Upper (D 0) (R 0) [112,5,130,257] 13 := by
  apply FastRouting.sound _ _ [112,5,130,257] 13 (by decide) (choices 1) [8,32,128] r2819 c2819
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1611
  · exact u1612
  · exact u1613

#print axioms u2819
end Delivery.IrregularNine14.P00
