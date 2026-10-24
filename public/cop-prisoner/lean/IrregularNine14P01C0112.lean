import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0049
import IrregularNine14P01C0050
import IrregularNine14P01C0051

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6720 : Route 9 := (fun mask => (mask,id))

def c6720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6720 : Upper (D 1) (R 1) [50,320,65,130] 13 := by
  apply FastRouting.sound _ _ [50,320,65,130] 13 (by decide) (choices 1) [4,8,32,128] r6720 c6720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2973
  · exact u2974
  · exact u2975
  · exact u2976

def r6721 : Route 9 := (fun mask => (mask,id))

def c6721 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6721 : Upper (D 1) (R 1) [50,320,65,132] 13 := by
  apply FastRouting.sound _ _ [50,320,65,132] 13 (by decide) (choices 1) [2,8,32,128] r6721 c6721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2977
  · exact u2978
  · exact u2979
  · exact u2980

def r6722 : Route 9 := (fun mask => (mask,id))

def c6722 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6722 : Upper (D 1) (R 1) [50,320,65,144] 13 := by
  apply FastRouting.sound _ _ [50,320,65,144] 13 (by decide) (choices 1) [2,4,8,32,128] r6722 c6722
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2981
  · exact u2982
  · exact u2983
  · exact u2984
  · exact u2985

def b6723 : PairBound 9 := { available := 188, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 70 137 188 188 252 188 444), lower := (rows 51 322 70 137 16 32 64 128 256), losses := [] }

theorem u6723 : Upper (D 1) (R 1) [50,320,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6723
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6724 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 70 140 185 185 249 185 441), lower := (rows 51 322 70 140 16 32 64 128 256), losses := [] }

theorem u6724 : Upper (D 1) (R 1) [50,320,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6724
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6725 : PairBound 9 := { available := 173, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 70 152 189 173 237 173 429), lower := (rows 51 322 70 152 16 32 64 128 256), losses := [] }

theorem u6725 : Upper (D 1) (R 1) [50,320,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6725
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6726 : Route 9 := (fun mask => (mask,id))

def c6726 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6726 : Upper (D 1) (R 1) [50,320,72,129] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129] 13 (by decide) (choices 1) [2,4,32,128] r6726 c6726
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2986
  · exact u2987
  · exact u2988
  · exact u2989

def r6727 : Route 9 := (fun mask => (mask,id))

def c6727 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6727 : Upper (D 1) (R 1) [50,320,72,130] 13 := by
  apply FastRouting.sound _ _ [50,320,72,130] 13 (by decide) (choices 1) [1,4,32,128] r6727 c6727
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u2990
  · exact u2991
  · exact u2992
  · exact u2993

def b6728 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 51 322 76 140 179 179 243 179 435), lower := (rows 51 322 76 140 16 32 64 128 256), losses := [] }

theorem u6728 : Upper (D 1) (R 1) [50,320,72,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6728
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6729 : Route 9 := (fun mask => (mask,id))

def c6729 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6729 : Upper (D 1) (R 1) [50,320,72,144] 13 := by
  apply FastRouting.sound _ _ [50,320,72,144] 13 (by decide) (choices 1) [1,2,4,32,128] r6729 c6729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2994
  · exact u2995
  · exact u2996
  · exact u2997
  · exact u2998

def r6730 : Route 9 := (fun mask => (mask,id))

def c6730 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 256 => 8 | _ => 0)

theorem u6730 : Upper (D 1) (R 1) [50,320,80,129] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129] 13 (by decide) (choices 1) [2,4,8,32,128] r6730 c6730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u2999
  · exact u3000
  · exact u3001
  · exact u3002
  · exact u3003

def r6731 : Route 9 := (fun mask => (mask,id))

def c6731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6731 : Upper (D 1) (R 1) [50,320,80,130] 13 := by
  apply FastRouting.sound _ _ [50,320,80,130] 13 (by decide) (choices 1) [1,4,8,32,128] r6731 c6731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3004
  · exact u3005
  · exact u3006
  · exact u3007
  · exact u3008

def r6732 : Route 9 := (fun mask => (mask,id))

def c6732 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6732 : Upper (D 1) (R 1) [50,320,80,132] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132] 13 (by decide) (choices 1) [1,2,8,32,128] r6732 c6732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3009
  · exact u3010
  · exact u3011
  · exact u3012
  · exact u3013

def r6733 : Route 9 := (fun mask => (mask,id))

def c6733 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6733 : Upper (D 1) (R 1) [50,320,80,160] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160] 13 (by decide) (choices 1) [1,2,4,8,128] r6733 c6733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3014
  · exact u3015
  · exact u3016
  · exact u3017
  · exact u3018

def r6734 : Route 9 := (fun mask => (mask,id))

def c6734 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6734 : Upper (D 1) (R 1) [50,320,129,130] 13 := by
  apply FastRouting.sound _ _ [50,320,129,130] 13 (by decide) (choices 1) [4,8,32,64] r6734 c6734
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3019
  · exact u3020
  · exact u3021
  · exact u3022

def b6735 : PairBound 9 := { available := 122, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 322 133 140 122 122 122 250 378), lower := (rows 51 322 133 140 16 32 64 128 256), losses := [] }

theorem u6735 : Upper (D 1) (R 1) [50,320,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6735
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6736 : Route 9 := (fun mask => (mask,id))

def c6736 : Nat → Fin 9 := (fun mask => match mask with | 128 => 7 | 256 => 8 | _ => 0)

theorem u6736 : Upper (D 1) (R 1) [50,320,129,144] 13 := by
  apply FastRouting.sound _ _ [50,320,129,144] 13 (by decide) (choices 1) [2,4,8,32,64] r6736 c6736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3023
  · exact u3024
  · exact u3025
  · exact u3026
  · exact u3027

def r6737 : Route 9 := (fun mask => (mask,id))

def c6737 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6737 : Upper (D 1) (R 1) [50,320,129,192] 13 := by
  apply FastRouting.sound _ _ [50,320,129,192] 13 (by decide) (choices 1) [2,4,8,32] r6737 c6737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3028
  · exact u3029
  · exact u3030
  · exact u3031

def b6738 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 51 322 134 140 121 121 121 249 377), lower := (rows 51 322 134 140 16 32 64 128 256), losses := [] }

theorem u6738 : Upper (D 1) (R 1) [50,320,130,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6738
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6739 : Route 9 := (fun mask => (mask,id))

def c6739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6739 : Upper (D 1) (R 1) [50,320,130,144] 13 := by
  apply FastRouting.sound _ _ [50,320,130,144] 13 (by decide) (choices 1) [1,4,8,32,64] r6739 c6739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3032
  · exact u3033
  · exact u3034
  · exact u3035
  · exact u3036

def r6740 : Route 9 := (fun mask => (mask,id))

def c6740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6740 : Upper (D 1) (R 1) [50,320,130,192] 13 := by
  apply FastRouting.sound _ _ [50,320,130,192] 13 (by decide) (choices 1) [1,4,8,32] r6740 c6740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3037
  · exact u3038
  · exact u3039
  · exact u3040

def b6741 : PairBound 9 := { available := 115, camps := [{ cop := 7, region := 12, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 140 140 115 115 115 243 371), lower := (rows 51 322 140 140 16 32 64 128 256), losses := [] }

theorem u6741 : Upper (D 1) (R 1) [50,320,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6741
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6742 : PairBound 9 := { available := 103, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 140 152 119 103 103 231 359), lower := (rows 51 322 140 152 16 32 64 128 256), losses := [] }

theorem u6742 : Upper (D 1) (R 1) [50,320,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6742
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6743 : PairBound 9 := { available := 55, camps := [{ cop := 3, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 140 200 55 55 119 183 311), lower := (rows 51 322 140 200 16 32 64 128 256), losses := [] }

theorem u6743 : Upper (D 1) (R 1) [50,320,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6743
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6744 : Route 9 := (fun mask => (mask,id))

def c6744 : Nat → Fin 9 := (fun mask => match mask with | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6744 : Upper (D 1) (R 1) [50,320,144,160] 13 := by
  apply FastRouting.sound _ _ [50,320,144,160] 13 (by decide) (choices 1) [1,2,4,8,64] r6744 c6744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3041
  · exact u3042
  · exact u3043
  · exact u3044
  · exact u3045

def r6745 : Route 9 := (fun mask => (mask,id))

def c6745 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u6745 : Upper (D 1) (R 1) [50,320,144,192] 13 := by
  apply FastRouting.sound _ _ [50,320,144,192] 13 (by decide) (choices 1) [1,2,4,8,32] r6745 c6745
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u3046
  · exact u3047
  · exact u3048
  · exact u3049
  · exact u3050

def b6746 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 70 26 496 480 480 480 480), lower := (rows 53 11 70 26 16 32 64 128 256), losses := [] }

theorem u6746 : Upper (D 1) (R 1) [52,9,66,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6746
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6747 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 70 56 466 482 450 450 450), lower := (rows 53 11 70 56 16 32 64 128 256), losses := [] }

theorem u6747 : Upper (D 1) (R 1) [52,9,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6747
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6748 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 8, targets := 16 }], pairs := [(3,4)], upper := (rows 53 11 70 74 432 432 496 432 432), lower := (rows 53 11 70 74 16 32 64 128 256), losses := [] }

theorem u6748 : Upper (D 1) (R 1) [52,9,66,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6748
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6749 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 70 88 434 418 482 418 418), lower := (rows 53 11 70 88 16 32 64 128 256), losses := [] }

theorem u6749 : Upper (D 1) (R 1) [52,9,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6749
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6750 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 433, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 70 138 496 496 496 496 496), lower := (rows 53 11 70 138 16 32 64 128 256), losses := [] }

theorem u6750 : Upper (D 1) (R 1) [52,9,66,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6750
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6751 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 70 152 498 482 482 482 482), lower := (rows 53 11 70 152 16 32 64 128 256), losses := [] }

theorem u6751 : Upper (D 1) (R 1) [52,9,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6751
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 434, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 53 11 70 200 434 434 498 434 434), lower := (rows 53 11 70 200 16 32 64 128 256), losses := [] }

theorem u6752 : Upper (D 1) (R 1) [52,9,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6752
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 177, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 70 266 240 240 240 240 496), lower := (rows 53 11 70 266 16 32 64 128 256), losses := [] }

theorem u6753 : Upper (D 1) (R 1) [52,9,66,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6753
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6754 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 70 280 242 226 226 226 482), lower := (rows 53 11 70 280 16 32 64 128 256), losses := [] }

theorem u6754 : Upper (D 1) (R 1) [52,9,66,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6754
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6755 : PairBound 9 := { available := 178, camps := [{ cop := 2, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 53 11 70 328 178 178 242 178 434), lower := (rows 53 11 70 328 16 32 64 128 256), losses := [] }

theorem u6755 : Upper (D 1) (R 1) [52,9,66,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6755
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6756 : Route 9 := (fun mask => (mask,id))

def c6756 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6756 : Upper (D 1) (R 1) [52,9,66,384] 13 := by
  apply FastRouting.sound _ _ [52,9,66,384] 13 (by decide) (choices 1) [2,32,64,128] r6756 c6756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3051
  · exact u3052
  · exact u3053
  · exact u3054

def b6757 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 196 26 498 482 482 482 482), lower := (rows 53 11 196 26 16 32 64 128 256), losses := [] }

theorem u6757 : Upper (D 1) (R 1) [52,9,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6757
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6758 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 196 56 466 482 450 450 450), lower := (rows 53 11 196 56 16 32 64 128 256), losses := [] }

theorem u6758 : Upper (D 1) (R 1) [52,9,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6758
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6759 : Route 9 := (fun mask => (mask,id))

def c6759 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6759 : Upper (D 1) (R 1) [52,9,192,66] 13 := by
  apply FastRouting.sound _ _ [52,9,192,66] 13 (by decide) (choices 1) [2,32,128,256] r6759 c6759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3055
  · exact u3056
  · exact u3057
  · exact u3058

def b6760 : PairBound 9 := { available := 418, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 196 88 434 418 482 418 418), lower := (rows 53 11 196 88 16 32 64 128 256), losses := [] }

theorem u6760 : Upper (D 1) (R 1) [52,9,192,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6760
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6761 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 8, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 196 200 306 306 370 434 306), lower := (rows 53 11 196 200 16 32 64 128 256), losses := [] }

theorem u6761 : Upper (D 1) (R 1) [52,9,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6761
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6762 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6762 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6762 : Upper (D 1) (R 1) [52,9,192,258] 13 := by
  apply FastRouting.sound _ _ [52,9,192,258] 13 (by decide) (choices 1) [2,32,64] r6762 c6762
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3059
  · exact u3060
  · exact u3061

def b6763 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 228, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 196 280 242 226 226 226 482), lower := (rows 53 11 196 280 16 32 64 128 256), losses := [] }

theorem u6763 : Upper (D 1) (R 1) [52,9,192,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6763
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6764 : Route 9 := (fun mask => (mask,id))

def c6764 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6764 : Upper (D 1) (R 1) [52,9,192,320] 13 := by
  apply FastRouting.sound _ _ [52,9,192,320] 13 (by decide) (choices 1) [2,32,128] r6764 c6764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3062
  · exact u3063
  · exact u3064

def b6765 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 262 26 240 224 224 224 480), lower := (rows 53 11 262 26 16 32 64 128 256), losses := [] }

theorem u6765 : Upper (D 1) (R 1) [52,9,258,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6765
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6766 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 262 56 210 226 194 194 450), lower := (rows 53 11 262 56 16 32 64 128 256), losses := [] }

theorem u6766 : Upper (D 1) (R 1) [52,9,258,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6766
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 241, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 262 74 240 240 240 240 496), lower := (rows 53 11 262 74 16 32 64 128 256), losses := [] }

theorem u6767 : Upper (D 1) (R 1) [52,9,258,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6767
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 262 88 242 226 226 226 482), lower := (rows 53 11 262 88 16 32 64 128 256), losses := [] }

theorem u6768 : Upper (D 1) (R 1) [52,9,258,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6768
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6769 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c6769 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6769 : Upper (D 1) (R 1) [52,9,258,192] 13 := by
  apply FastRouting.sound _ _ [52,9,258,192] 13 (by decide) (choices 1) [2,32,64] r6769 c6769
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3065
  · exact u3066
  · exact u3067

def b6770 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 26 242 226 226 226 482), lower := (rows 53 11 324 26 16 32 64 128 256), losses := [] }

theorem u6770 : Upper (D 1) (R 1) [52,9,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6770
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6771 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 324 56 210 226 194 194 450), lower := (rows 53 11 324 56 16 32 64 128 256), losses := [] }

theorem u6771 : Upper (D 1) (R 1) [52,9,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6771
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6772 : Route 9 := (fun mask => (mask,id))

def c6772 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6772 : Upper (D 1) (R 1) [52,9,320,66] 13 := by
  apply FastRouting.sound _ _ [52,9,320,66] 13 (by decide) (choices 1) [2,32,128] r6772 c6772
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3068
  · exact u3069
  · exact u3070

def b6773 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 324 88 178 162 226 162 418), lower := (rows 53 11 324 88 16 32 64 128 256), losses := [] }

theorem u6773 : Upper (D 1) (R 1) [52,9,320,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6773
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6774 : Route 9 := (fun mask => (mask,id))

def c6774 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u6774 : Upper (D 1) (R 1) [52,9,320,130] 13 := by
  apply FastRouting.sound _ _ [52,9,320,130] 13 (by decide) (choices 1) [2,32,64,128] r6774 c6774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3071
  · exact u3072
  · exact u3073
  · exact u3074

def b6775 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 53 11 324 152 242 226 226 226 482), lower := (rows 53 11 324 152 16 32 64 128 256), losses := [] }

theorem u6775 : Upper (D 1) (R 1) [52,9,320,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6775
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r6776 : Route 9 := (fun mask => (mask,id))

def c6776 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u6776 : Upper (D 1) (R 1) [52,9,320,192] 13 := by
  apply FastRouting.sound _ _ [52,9,320,192] 13 (by decide) (choices 1) [2,32,128] r6776 c6776
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3075
  · exact u3076
  · exact u3077

def b6777 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 70 11 496 480 480 480 480), lower := (rows 53 26 70 11 16 32 64 128 256), losses := [] }

theorem u6777 : Upper (D 1) (R 1) [52,24,66,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6777
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6778 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 41 466 482 450 450 450), lower := (rows 53 26 70 41 16 32 64 128 256), losses := [] }

theorem u6778 : Upper (D 1) (R 1) [52,24,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6778
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b6779 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 42 465 481 449 449 449), lower := (rows 53 26 70 42 16 32 64 128 256), losses := [] }

theorem u6779 : Upper (D 1) (R 1) [52,24,66,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b6779
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u6779
end Delivery.IrregularNine14.P01
