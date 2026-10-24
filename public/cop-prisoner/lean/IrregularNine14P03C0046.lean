import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0013
import IrregularNine14P03C0014

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2760 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 41 280 241 209 209 465), lower := (rows 35 7 196 41 280 32 64 128 256), losses := [] }

theorem u2760 : Upper (D 3) (R 3) [34,5,192,33,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2760
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2761 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 41 336 185 217 153 409), lower := (rows 35 7 196 41 336 32 64 128 256), losses := [] }

theorem u2761 : Upper (D 3) (R 3) [34,5,192,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2761
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2762 : PairBound 9 := { available := 393, camps := [{ cop := 4, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 56 81 425 457 393 393), lower := (rows 35 7 196 56 81 32 64 128 256), losses := [] }

theorem u2762 : Upper (D 3) (R 3) [34,5,192,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2762
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2763 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 56 88 417 449 385 385), lower := (rows 35 7 196 56 88 32 64 128 256), losses := [] }

theorem u2763 : Upper (D 3) (R 3) [34,5,192,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2763
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2764 : PairBound 9 := { available := 265, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 196 56 208 297 329 393 265), lower := (rows 35 7 196 56 208 32 64 128 256), losses := [] }

theorem u2764 : Upper (D 3) (R 3) [34,5,192,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2764
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2765 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2765 : Upper (D 3) (R 3) [34,5,192,48,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,257] 13 (by decide) (choices 1) [1,8,64] r2765 c2765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u805
  · exact u806
  · exact u807

def b2766 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 198, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 196 56 280 225 193 193 449), lower := (rows 35 7 196 56 280 32 64 128 256), losses := [] }

theorem u2766 : Upper (D 3) (R 3) [34,5,192,48,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2766
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2767 : Route 9 := (fun mask => (mask,id))

def c2767 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2767 : Upper (D 3) (R 3) [34,5,192,48,320] 13 := by
  apply FastRouting.sound _ _ [34,5,192,48,320] 13 (by decide) (choices 1) [1,8,128] r2767 c2767
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u808
  · exact u809
  · exact u810

def b2768 : PairBound 9 := { available := 305, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 152 305 369 433 305), lower := (rows 35 7 196 73 152 32 64 128 256), losses := [] }

theorem u2768 : Upper (D 3) (R 3) [34,5,192,65,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2768
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2769 : PairBound 9 := { available := 281, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 176 313 345 409 281), lower := (rows 35 7 196 73 176 32 64 128 256), losses := [] }

theorem u2769 : Upper (D 3) (R 3) [34,5,192,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2769
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2770 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 273 184 248 184 440), lower := (rows 35 7 196 73 273 32 64 128 256), losses := [] }

theorem u2770 : Upper (D 3) (R 3) [34,5,192,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2770
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2771 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 280 177 241 177 433), lower := (rows 35 7 196 73 280 32 64 128 256), losses := [] }

theorem u2771 : Upper (D 3) (R 3) [34,5,192,65,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2771
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2772 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 304 185 217 153 409), lower := (rows 35 7 196 73 304 32 64 128 256), losses := [] }

theorem u2772 : Upper (D 3) (R 3) [34,5,192,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2772
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2773 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 196 73 400 57 121 185 313), lower := (rows 35 7 196 73 400 32 64 128 256), losses := [] }

theorem u2773 : Upper (D 3) (R 3) [34,5,192,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2773
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2774 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 88 152 289 353 417 289), lower := (rows 35 7 196 88 152 32 64 128 256), losses := [] }

theorem u2774 : Upper (D 3) (R 3) [34,5,192,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2774
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2775 : Route 9 := (fun mask => (mask,id))

def c2775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2775 : Upper (D 3) (R 3) [34,5,192,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,160] 13 (by decide) (choices 1) [1,8,256] r2775 c2775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u811
  · exact u812
  · exact u813

def r2776 : Route 9 := (fun mask => (mask,id))

def c2776 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2776 : Upper (D 3) (R 3) [34,5,192,80,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,257] 13 (by decide) (choices 1) [1,8,128] r2776 c2776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u814
  · exact u815
  · exact u816

def b2777 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 88 280 161 225 161 417), lower := (rows 35 7 196 88 280 32 64 128 256), losses := [] }

theorem u2777 : Upper (D 3) (R 3) [34,5,192,80,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2777
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2778 : Route 9 := (fun mask => (mask,id))

def c2778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2778 : Upper (D 3) (R 3) [34,5,192,80,288] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,288] 13 (by decide) (choices 1) [1,8,128] r2778 c2778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u817
  · exact u818
  · exact u819

def r2779 : Route 9 := (fun mask => (mask,id))

def c2779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2779 : Upper (D 3) (R 3) [34,5,192,80,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,80,384] 13 (by decide) (choices 1) [1,8] r2779 c2779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u820
  · exact u821

def r2780 : Route 9 := (fun mask => (mask,id))

def c2780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2780 : Upper (D 3) (R 3) [34,5,192,96,257] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,257] 13 (by decide) (choices 1) [1,8,16,128] r2780 c2780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u822
  · exact u823
  · exact u824
  · exact u825

def r2781 : Route 9 := (fun mask => (mask,id))

def c2781 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2781 : Upper (D 3) (R 3) [34,5,192,96,264] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,264] 13 (by decide) (choices 1) [1,16,128] r2781 c2781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u826
  · exact u827
  · exact u828

def r2782 : Route 9 := (fun mask => (mask,id))

def c2782 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2782 : Upper (D 3) (R 3) [34,5,192,96,384] 13 := by
  apply FastRouting.sound _ _ [34,5,192,96,384] 13 (by decide) (choices 1) [1,8,16] r2782 c2782
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u829
  · exact u830
  · exact u831

def b2783 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 273 57 121 185 313), lower := (rows 35 7 196 200 273 32 64 128 256), losses := [] }

theorem u2783 : Upper (D 3) (R 3) [34,5,192,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2783
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2784 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 280 49 113 177 305), lower := (rows 35 7 196 200 280 32 64 128 256), losses := [] }

theorem u2784 : Upper (D 3) (R 3) [34,5,192,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2784
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2785 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 196 200 304 57 89 153 281), lower := (rows 35 7 196 200 304 32 64 128 256), losses := [] }

theorem u2785 : Upper (D 3) (R 3) [34,5,192,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2785
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2786 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 268 25 49 224 192 192 448), lower := (rows 35 7 268 25 49 32 64 128 256), losses := [] }

theorem u2786 : Upper (D 3) (R 3) [34,5,264,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2786
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2787 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 268 25 81 224 224 224 480), lower := (rows 35 7 268 25 81 32 64 128 256), losses := [] }

theorem u2787 : Upper (D 3) (R 3) [34,5,264,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2787
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2788 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 25 112 225 193 193 449), lower := (rows 35 7 268 25 112 32 64 128 256), losses := [] }

theorem u2788 : Upper (D 3) (R 3) [34,5,264,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2788
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2789 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2789 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2789 : Upper (D 3) (R 3) [34,5,264,17,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,17,192] 13 (by decide) (choices 1) [1,64] r2789 c2789
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u832
  · exact u833

def b2790 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 73 49 240 208 208 464), lower := (rows 35 7 268 73 49 32 64 128 256), losses := [] }

theorem u2790 : Upper (D 3) (R 3) [34,5,264,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2790
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2791 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 7 268 73 81 176 240 176 432), lower := (rows 35 7 268 73 81 32 64 128 256), losses := [] }

theorem u2791 : Upper (D 3) (R 3) [34,5,264,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2791
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2792 : Route 9 := (fun mask => (mask,id))

def c2792 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2792 : Upper (D 3) (R 3) [34,5,264,65,96] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,96] 13 (by decide) (choices 1) [1,16,128] r2792 c2792
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u834
  · exact u835
  · exact u836

def r2793 : Route 9 := (fun mask => (mask,id))

def c2793 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2793 : Upper (D 3) (R 3) [34,5,264,65,129] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,129] 13 (by decide) (choices 1) [16,64,128] r2793 c2793
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u837
  · exact u838
  · exact u839

def r2794 : Route 9 := (fun mask => (mask,id))

def c2794 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u2794 : Upper (D 3) (R 3) [34,5,264,65,160] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,160] 13 (by decide) (choices 1) [1,16,64,128] r2794 c2794
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u840
  · exact u841
  · exact u842
  · exact u843

def r2795 : Route 9 := (fun mask => (mask,id))

def c2795 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2795 : Upper (D 3) (R 3) [34,5,264,65,192] 13 := by
  apply FastRouting.sound _ _ [34,5,264,65,192] 13 (by decide) (choices 1) [1,16,128] r2795 c2795
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u844
  · exact u845
  · exact u846

def b2796 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 88 49 225 193 193 449), lower := (rows 35 7 268 88 49 32 64 128 256), losses := [] }

theorem u2796 : Upper (D 3) (R 3) [34,5,264,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2796
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2797 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 81 161 225 161 417), lower := (rows 35 7 268 88 81 32 64 128 256), losses := [] }

theorem u2797 : Upper (D 3) (R 3) [34,5,264,80,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2797
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2798 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 112 161 193 129 385), lower := (rows 35 7 268 88 112 32 64 128 256), losses := [] }

theorem u2798 : Upper (D 3) (R 3) [34,5,264,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2798
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2799 : Route 9 := (fun mask => (mask,id))

def c2799 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2799 : Upper (D 3) (R 3) [34,5,264,80,129] 13 := by
  apply FastRouting.sound _ _ [34,5,264,80,129] 13 (by decide) (choices 1) [1,64,128] r2799 c2799
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u847
  · exact u848
  · exact u849

def r2800 : Route 9 := (fun mask => (mask,id))

def c2800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2800 : Upper (D 3) (R 3) [34,5,264,80,160] 13 := by
  apply FastRouting.sound _ _ [34,5,264,80,160] 13 (by decide) (choices 1) [1,64,128] r2800 c2800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u850
  · exact u851
  · exact u852

def b2801 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 268 88 208 161 225 161 417), lower := (rows 35 7 268 88 208 32 64 128 256), losses := [] }

theorem u2801 : Upper (D 3) (R 3) [34,5,264,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2802 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 200 49 241 209 209 465), lower := (rows 35 7 268 200 49 32 64 128 256), losses := [] }

theorem u2802 : Upper (D 3) (R 3) [34,5,264,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2803 : Route 9 := (fun mask => (mask,id))

def c2803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2803 : Upper (D 3) (R 3) [34,5,264,192,65] 13 := by
  apply FastRouting.sound _ _ [34,5,264,192,65] 13 (by decide) (choices 1) [1,16,128] r2803 c2803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u853
  · exact u854
  · exact u855

def r2804 : Route 9 := (fun mask => (mask,id))

def c2804 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2804 : Upper (D 3) (R 3) [34,5,264,192,96] 13 := by
  apply FastRouting.sound _ _ [34,5,264,192,96] 13 (by decide) (choices 1) [1,16,128] r2804 c2804
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u856
  · exact u857
  · exact u858

def b2805 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 268 200 208 49 113 177 305), lower := (rows 35 7 268 200 208 32 64 128 256), losses := [] }

theorem u2805 : Upper (D 3) (R 3) [34,5,264,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2805
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2806 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 324 25 25 224 224 224 480), lower := (rows 35 7 324 25 25 32 64 128 256), losses := [] }

theorem u2806 : Upper (D 3) (R 3) [34,5,320,17,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2806
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2807 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 25 49 232 200 200 456), lower := (rows 35 7 324 25 49 32 64 128 256), losses := [] }

theorem u2807 : Upper (D 3) (R 3) [34,5,320,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2808 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 24, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 324 25 56 225 193 193 449), lower := (rows 35 7 324 25 56 32 64 128 256), losses := [] }

theorem u2808 : Upper (D 3) (R 3) [34,5,320,17,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2809 : PairBound 9 := { available := 168, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 324 25 81 168 232 168 424), lower := (rows 35 7 324 25 81 32 64 128 256), losses := [] }

theorem u2809 : Upper (D 3) (R 3) [34,5,320,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2809
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2810 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 163, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 324 25 88 161 225 161 417), lower := (rows 35 7 324 25 88 32 64 128 256), losses := [] }

theorem u2810 : Upper (D 3) (R 3) [34,5,320,17,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2811 : PairBound 9 := { available := 137, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 25 112 169 201 137 393), lower := (rows 35 7 324 25 112 32 64 128 256), losses := [] }

theorem u2811 : Upper (D 3) (R 3) [34,5,320,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2811
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2812 : PairBound 9 := { available := 232, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 324 25 145 232 232 232 488), lower := (rows 35 7 324 25 145 32 64 128 256), losses := [] }

theorem u2812 : Upper (D 3) (R 3) [34,5,320,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2813 : Route 9 := (fun mask => (mask,id))

def c2813 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2813 : Upper (D 3) (R 3) [34,5,320,17,136] 13 := by
  apply FastRouting.sound _ _ [34,5,320,17,136] 13 (by decide) (choices 1) [1,64,128] r2813 c2813
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u859
  · exact u860
  · exact u861

def b2814 : PairBound 9 := { available := 201, camps := [{ cop := 3, region := 454, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 25 176 233 201 201 457), lower := (rows 35 7 324 25 176 32 64 128 256), losses := [] }

theorem u2814 : Upper (D 3) (R 3) [34,5,320,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2814
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2815 : Route 9 := (fun mask => (mask,id))

def c2815 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2815 : Upper (D 3) (R 3) [34,5,320,17,192] 13 := by
  apply FastRouting.sound _ _ [34,5,320,17,192] 13 (by decide) (choices 1) [1,8,128] r2815 c2815
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u862
  · exact u863
  · exact u864

def b2816 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 41 88 177 209 145 401), lower := (rows 35 7 324 41 88 32 64 128 256), losses := [] }

theorem u2816 : Upper (D 3) (R 3) [34,5,320,33,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2817 : PairBound 9 := { available := 216, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 41 145 248 216 216 472), lower := (rows 35 7 324 41 145 32 64 128 256), losses := [] }

theorem u2817 : Upper (D 3) (R 3) [34,5,320,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2817
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2818 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 41 152 241 209 209 465), lower := (rows 35 7 324 41 152 32 64 128 256), losses := [] }

theorem u2818 : Upper (D 3) (R 3) [34,5,320,33,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2819 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 324 41 208 185 217 153 409), lower := (rows 35 7 324 41 208 32 64 128 256), losses := [] }

theorem u2819 : Upper (D 3) (R 3) [34,5,320,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2819
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2819
end Delivery.IrregularNine14.P03
