import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0010

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2760 : Route 9 := (fun mask => (mask,id))

def c2760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2760 : Upper (D 5) (R 5) [6,65,136,18,36,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,36,256] 13 (by decide) (choices 1) [1,8,32] r2760 c2760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u614
  · exact u615
  · exact u616

def b2761 : PairBound 9 := { available := 40, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 140 26 276 33 104 168 296), lower := (rows 7 67 140 26 276 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 28 35 72 136 264), good := (rows 53 97 476 508 276 33 64 128 256) }] }

theorem u2761 : Upper (D 5) (R 5) [6,65,136,18,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2761
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 33, camps := [], pairs := [(1,2),(4,1)], upper := (rows 7 67 140 26 276 40 97 161 289), lower := (rows 7 67 140 26 276 40 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 8 17 44 65 129 257), good := (rows 501 465 172 56 308 40 64 128 256) },{ target := 2, region := (rows 1 3 0 8 16 44 65 129 257), good := (rows 483 451 168 58 304 40 64 128 256) }] }

theorem u2762 : Upper (D 5) (R 5) [6,65,136,18,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2762
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 44, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 67 140 26 304 33 108 172 300), lower := (rows 7 67 140 26 304 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 24 35 72 136 264), good := (rows 37 97 476 508 304 33 64 128 256) }] }

theorem u2763 : Upper (D 5) (R 5) [6,65,136,18,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2763
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2764 : Route 9 := (fun mask => (mask,id))

def c2764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2764 : Upper (D 5) (R 5) [6,65,136,18,288,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,288,4] 13 (by decide) (choices 1) [1,8,32] r2764 c2764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u617
  · exact u618
  · exact u619

def r2765 : Route 9 := (fun mask => (mask,id))

def c2765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2765 : Upper (D 5) (R 5) [6,65,136,18,288,8] 13 := by
  apply FastRouting.sound _ _ [6,65,136,18,288,8] 13 (by decide) (choices 1) [1,4,32] r2765 c2765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u620
  · exact u621
  · exact u622

def b2766 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 28 49 34 360 424 296), lower := (rows 7 67 140 28 49 34 64 128 256), losses := [] }

theorem u2766 : Upper (D 5) (R 5) [6,65,136,20,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2766
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2767 : PairBound 9 := { available := 290, camps := [{ cop := 0, region := 56, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 67 140 28 49 40 354 418 290), lower := (rows 7 67 140 28 49 40 64 128 256), losses := [] }

theorem u2767 : Upper (D 5) (R 5) [6,65,136,20,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2767
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2768 : Route 9 := (fun mask => (mask,id))

def c2768 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2768 : Upper (D 5) (R 5) [6,65,136,20,33,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,33,256] 13 (by decide) (choices 1) [2,8,32] r2768 c2768
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u623
  · exact u624
  · exact u625

def b2769 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 396, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 28 50 33 360 424 296), lower := (rows 7 67 140 28 50 33 64 128 256), losses := [] }

theorem u2769 : Upper (D 5) (R 5) [6,65,136,20,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2769
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 56, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 67 140 28 50 40 353 417 289), lower := (rows 7 67 140 28 50 40 64 128 256), losses := [] }

theorem u2770 : Upper (D 5) (R 5) [6,65,136,20,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2770
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2771 : Route 9 := (fun mask => (mask,id))

def c2771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2771 : Upper (D 5) (R 5) [6,65,136,20,34,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,34,256] 13 (by decide) (choices 1) [1,8,32] r2771 c2771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u626
  · exact u627
  · exact u628

def b2772 : PairBound 9 := { available := 40, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 28 273 34 104 168 296), lower := (rows 7 67 140 28 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 28 24 16 35 80 144 272), good := (rows 38 98 140 476 508 34 64 128 256) }] }

theorem u2772 : Upper (D 5) (R 5) [6,65,136,20,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2772
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 34, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 28 273 40 98 162 290), lower := (rows 7 67 140 28 273 40 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 60 65 129 257), good := (rows 486 450 172 60 508 40 64 128 256) }] }

theorem u2773 : Upper (D 5) (R 5) [6,65,136,20,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2773
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 40, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 67 140 28 274 33 104 168 296), lower := (rows 7 67 140 28 274 33 64 128 256), losses := [{ target := 1, region := (rows 1 0 28 24 16 35 80 144 272), good := (rows 37 97 140 476 508 33 64 128 256) }] }

theorem u2774 : Upper (D 5) (R 5) [6,65,136,20,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2774
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2775 : PairBound 9 := { available := 33, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 28 274 40 97 161 289), lower := (rows 7 67 140 28 274 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 19 44 65 129 257), good := (rows 499 467 168 56 274 40 64 128 256) }] }

theorem u2775 : Upper (D 5) (R 5) [6,65,136,20,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2775
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2776 : Route 9 := (fun mask => (mask,id))

def c2776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2776 : Upper (D 5) (R 5) [6,65,136,20,288,1] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,288,1] 13 (by decide) (choices 1) [2,8,32] r2776 c2776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u629
  · exact u630
  · exact u631

def r2777 : Route 9 := (fun mask => (mask,id))

def c2777 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2777 : Upper (D 5) (R 5) [6,65,136,20,288,2] 13 := by
  apply FastRouting.sound _ _ [6,65,136,20,288,2] 13 (by decide) (choices 1) [1,8,32] r2777 c2777
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u632
  · exact u633
  · exact u634

def b2778 : PairBound 9 := { available := 35, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 28 304 40 99 163 291), lower := (rows 7 67 140 28 304 40 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 17 44 65 129 257), good := (rows 499 467 168 56 304 40 64 128 256) }] }

theorem u2778 : Upper (D 5) (R 5) [6,65,136,20,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2778
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2779 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 41 50 36 344 408 280), lower := (rows 7 67 140 41 50 36 64 128 256), losses := [] }

theorem u2779 : Upper (D 5) (R 5) [6,65,136,33,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2779
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2780 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 140 41 50 40 340 404 276), lower := (rows 7 67 140 41 50 40 64 128 256), losses := [] }

theorem u2780 : Upper (D 5) (R 5) [6,65,136,33,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2780
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2781 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 455, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 41 50 48 332 396 268), lower := (rows 7 67 140 41 50 48 64 128 256), losses := [] }

theorem u2781 : Upper (D 5) (R 5) [6,65,136,33,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2781
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2782 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0)], upper := (rows 7 67 140 41 50 288 92 156 284), lower := (rows 7 67 140 41 50 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 17 300 72 136 264), good := (rows 54 82 492 508 50 288 64 128 288) }] }

theorem u2782 : Upper (D 5) (R 5) [6,65,136,33,34,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2782
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2783 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 41 52 34 344 408 280), lower := (rows 7 67 140 41 52 34 64 128 256), losses := [] }

theorem u2783 : Upper (D 5) (R 5) [6,65,136,33,36,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2783
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 274, camps := [{ cop := 4, region := 323, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 140 41 52 40 338 402 274), lower := (rows 7 67 140 41 52 40 64 128 256), losses := [] }

theorem u2784 : Upper (D 5) (R 5) [6,65,136,33,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2784
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 41 52 48 330 394 266), lower := (rows 7 67 140 41 52 48 64 128 256), losses := [] }

theorem u2785 : Upper (D 5) (R 5) [6,65,136,33,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2785
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2786 : Route 9 := (fun mask => (mask,id))

def c2786 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2786 : Upper (D 5) (R 5) [6,65,136,33,36,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,33,36,256] 13 (by decide) (choices 1) [2,8,16] r2786 c2786
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u635
  · exact u636
  · exact u637

def b2787 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 41 274 36 120 184 312), lower := (rows 7 67 140 41 274 36 64 128 256), losses := [] }

theorem u2787 : Upper (D 5) (R 5) [6,65,136,33,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2787
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 140 41 274 40 116 180 308), lower := (rows 7 67 140 41 274 40 64 128 256), losses := [] }

theorem u2788 : Upper (D 5) (R 5) [6,65,136,33,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2788
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2789 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 41 274 48 108 172 300), lower := (rows 7 67 140 41 274 48 64 128 256), losses := [] }

theorem u2789 : Upper (D 5) (R 5) [6,65,136,33,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2789
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2790 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 41 276 34 120 184 312), lower := (rows 7 67 140 41 276 34 64 128 256), losses := [] }

theorem u2790 : Upper (D 5) (R 5) [6,65,136,33,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2790
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 140 41 276 40 114 178 306), lower := (rows 7 67 140 41 276 40 64 128 256), losses := [] }

theorem u2791 : Upper (D 5) (R 5) [6,65,136,33,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2791
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2792 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 66, targets := 4 }], pairs := [(1,2)], upper := (rows 7 67 140 41 276 48 106 170 298), lower := (rows 7 67 140 41 276 48 64 128 256), losses := [] }

theorem u2792 : Upper (D 5) (R 5) [6,65,136,33,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2792
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2793 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 41 280 34 116 180 308), lower := (rows 7 67 140 41 280 34 64 128 256), losses := [] }

theorem u2793 : Upper (D 5) (R 5) [6,65,136,33,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2793
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2794 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 41 280 36 114 178 306), lower := (rows 7 67 140 41 280 36 64 128 256), losses := [] }

theorem u2794 : Upper (D 5) (R 5) [6,65,136,33,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2794
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2795 : PairBound 9 := { available := 38, camps := [], pairs := [(2,0)], upper := (rows 7 67 140 41 280 48 102 166 294), lower := (rows 7 67 140 41 280 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 24 60 65 129 257), good := (rows 486 450 188 508 316 48 64 128 256) }] }

theorem u2795 : Upper (D 5) (R 5) [6,65,136,33,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2795
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2796 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 41 304 34 92 156 284), lower := (rows 7 67 140 41 304 34 64 128 256), losses := [] }

theorem u2796 : Upper (D 5) (R 5) [6,65,136,33,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2796
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 26, camps := [{ cop := 3, region := 338, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 67 140 41 304 36 90 154 282), lower := (rows 7 67 140 41 304 36 64 128 256), losses := [] }

theorem u2797 : Upper (D 5) (R 5) [6,65,136,33,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2797
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 67 140 41 304 40 86 150 278), lower := (rows 7 67 140 41 304 40 64 128 256), losses := [] }

theorem u2798 : Upper (D 5) (R 5) [6,65,136,33,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2798
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2799 : PairBound 9 := { available := 14, camps := [{ cop := 8, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 41 304 48 78 142 270), lower := (rows 7 67 140 41 304 48 64 128 256), losses := [] }

theorem u2799 : Upper (D 5) (R 5) [6,65,136,33,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2799
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2800 : PairBound 9 := { available := 280, camps := [{ cop := 0, region := 48, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 67 140 42 49 36 344 408 280), lower := (rows 7 67 140 42 49 36 64 128 256), losses := [] }

theorem u2800 : Upper (D 5) (R 5) [6,65,136,34,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2801 : PairBound 9 := { available := 276, camps := [{ cop := 0, region := 56, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 67 140 42 49 40 340 404 276), lower := (rows 7 67 140 42 49 40 64 128 256), losses := [] }

theorem u2801 : Upper (D 5) (R 5) [6,65,136,34,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 389, targets := 32 }], pairs := [(0,5)], upper := (rows 7 67 140 42 49 48 332 396 268), lower := (rows 7 67 140 42 49 48 64 128 256), losses := [] }

theorem u2802 : Upper (D 5) (R 5) [6,65,136,34,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2803 : Route 9 := (fun mask => (mask,id))

def c2803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2803 : Upper (D 5) (R 5) [6,65,136,34,33,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,33,256] 13 (by decide) (choices 1) [4,8,16] r2803 c2803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u638
  · exact u639
  · exact u640

def b2804 : PairBound 9 := { available := 280, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 52 33 344 408 280), lower := (rows 7 67 140 42 52 33 64 128 256), losses := [] }

theorem u2804 : Upper (D 5) (R 5) [6,65,136,34,36,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2805 : PairBound 9 := { available := 273, camps := [{ cop := 4, region := 323, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 67 140 42 52 40 337 401 273), lower := (rows 7 67 140 42 52 40 64 128 256), losses := [] }

theorem u2805 : Upper (D 5) (R 5) [6,65,136,34,36,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 67 140 42 52 48 329 393 265), lower := (rows 7 67 140 42 52 48 64 128 256), losses := [] }

theorem u2806 : Upper (D 5) (R 5) [6,65,136,34,36,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2806
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2807 : Route 9 := (fun mask => (mask,id))

def c2807 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2807 : Upper (D 5) (R 5) [6,65,136,34,36,256] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,36,256] 13 (by decide) (choices 1) [1,8,16] r2807 c2807
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u641
  · exact u642
  · exact u643

def b2808 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 40, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 67 140 42 273 36 120 184 312), lower := (rows 7 67 140 42 273 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 11 16 53 80 144 272), good := (rows 46 106 172 42 508 36 64 128 256) }] }

theorem u2808 : Upper (D 5) (R 5) [6,65,136,34,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 140 42 273 40 116 180 308), lower := (rows 7 67 140 42 273 40 64 128 256), losses := [] }

theorem u2809 : Upper (D 5) (R 5) [6,65,136,34,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 44, camps := [{ cop := 3, region := 132, targets := 1 }], pairs := [(2,0)], upper := (rows 7 67 140 42 273 48 108 172 300), lower := (rows 7 67 140 42 273 48 64 128 256), losses := [] }

theorem u2810 : Upper (D 5) (R 5) [6,65,136,34,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 276 33 120 184 312), lower := (rows 7 67 140 42 276 33 64 128 256), losses := [] }

theorem u2811 : Upper (D 5) (R 5) [6,65,136,34,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 140 42 276 40 113 177 305), lower := (rows 7 67 140 42 276 40 64 128 256), losses := [] }

theorem u2812 : Upper (D 5) (R 5) [6,65,136,34,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2813 : Route 9 := (fun mask => (mask,id))

def c2813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2813 : Upper (D 5) (R 5) [6,65,136,34,260,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,260,16] 13 (by decide) (choices 1) [1,8,32] r2813 c2813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u644
  · exact u645
  · exact u646

def b2814 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 280 33 116 180 308), lower := (rows 7 67 140 42 280 33 64 128 256), losses := [] }

theorem u2814 : Upper (D 5) (R 5) [6,65,136,34,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2815 : Route 9 := (fun mask => (mask,id))

def c2815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2815 : Upper (D 5) (R 5) [6,65,136,34,264,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,264,4] 13 (by decide) (choices 1) [1,16,32] r2815 c2815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u647
  · exact u648
  · exact u649

def r2816 : Route 9 := (fun mask => (mask,id))

def c2816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2816 : Upper (D 5) (R 5) [6,65,136,34,264,16] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,264,16] 13 (by decide) (choices 1) [1,4,32] r2816 c2816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u650
  · exact u651
  · exact u652

def b2817 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 67 140 42 304 33 92 156 284), lower := (rows 7 67 140 42 304 33 64 128 256), losses := [] }

theorem u2817 : Upper (D 5) (R 5) [6,65,136,34,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r2818 : Route 9 := (fun mask => (mask,id))

def c2818 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2818 : Upper (D 5) (R 5) [6,65,136,34,288,4] 13 := by
  apply FastRouting.sound _ _ [6,65,136,34,288,4] 13 (by decide) (choices 1) [1,8,16] r2818 c2818
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u653
  · exact u654
  · exact u655

def b2819 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 40, targets := 5 }], pairs := [(3,0),(3,2)], upper := (rows 7 67 140 42 304 40 85 149 277), lower := (rows 7 67 140 42 304 40 64 128 256), losses := [] }

theorem u2819 : Upper (D 5) (R 5) [6,65,136,34,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b2819
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P05
