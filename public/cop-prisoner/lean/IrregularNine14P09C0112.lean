import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0050
import IrregularNine14P09C0051
import IrregularNine14P09C0052

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r6720 : Route 9 := (fun mask => (mask,id))

def c6720 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6720 : Upper (D 9) (R 9) [6,9,96,144,33] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,33] 13 (by decide) (choices 1) [64,128,256] r6720 c6720
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3023
  · exact u3024
  · exact u3025

def b6721 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 385 },{ cop := 4, region := 4, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7),(4,8)], upper := (rows 7 11 100 152 112 417 449 385 385), lower := (rows 7 11 100 152 112 32 64 128 256), losses := [] }

theorem u6721 : Upper (D 9) (R 9) [6,9,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6721 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6722 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 10, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(3,5),(3,6)], upper := (rows 7 11 100 152 145 352 352 480 352), lower := (rows 7 11 100 152 145 32 64 128 256), losses := [] }

theorem u6722 : Upper (D 9) (R 9) [6,9,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6722 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6723 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 11 100 152 176 353 321 449 321), lower := (rows 7 11 100 152 176 32 64 128 256), losses := [] }

theorem u6723 : Upper (D 9) (R 9) [6,9,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6723 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6724 : Route 9 := (fun mask => (mask,id))

def c6724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6724 : Upper (D 9) (R 9) [6,9,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,257] 13 (by decide) (choices 1) [64,128,256] r6724 c6724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3026
  · exact u3027
  · exact u3028

def r6725 : Route 9 := (fun mask => (mask,id))

def c6725 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6725 : Upper (D 9) (R 9) [6,9,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,9,96,144,288] 13 (by decide) (choices 1) [1,64,128,256] r6725 c6725
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3029
  · exact u3030
  · exact u3031
  · exact u3032

def b6726 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 353 },{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7),(3,0),(3,5),(3,6),(3,8)], upper := (rows 7 11 100 152 400 353 353 481 353), lower := (rows 7 11 100 152 400 32 64 128 256), losses := [] }

theorem u6726 : Upper (D 9) (R 9) [6,9,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6727 : PairBound 9 := { available := 400, camps := [{ cop := 4, region := 428, targets := 1 },{ cop := 4, region := 426, targets := 64 },{ cop := 0, region := 464, targets := 32 }], pairs := [(1,6),(2,0),(3,0),(3,6),(4,5)], upper := (rows 7 11 100 168 81 432 464 400 400), lower := (rows 7 11 100 168 81 32 64 128 256), losses := [] }

theorem u6727 : Upper (D 9) (R 9) [6,9,96,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6727 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6728 : Route 9 := (fun mask => (mask,id))

def c6728 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6728 : Upper (D 9) (R 9) [6,9,96,160,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,129] 13 (by decide) (choices 1) [16,64,256] r6728 c6728
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3033
  · exact u3034
  · exact u3035

def r6729 : Route 9 := (fun mask => (mask,id))

def c6729 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6729 : Upper (D 9) (R 9) [6,9,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,192] 13 (by decide) (choices 1) [1,16,256] r6729 c6729
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3036
  · exact u3037
  · exact u3038

def r6730 : Route 9 := (fun mask => (mask,id))

def c6730 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6730 : Upper (D 9) (R 9) [6,9,96,160,257] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257] 13 (by decide) (choices 1) [16,64,128,256] r6730 c6730
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3039
  · exact u3040
  · exact u3041
  · exact u3042

def r6731 : Route 9 := (fun mask => (mask,id))

def c6731 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u6731 : Upper (D 9) (R 9) [6,9,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,320] 13 (by decide) (choices 1) [1,16,128,256] r6731 c6731
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3043
  · exact u3044
  · exact u3045
  · exact u3046

def r6732 : Route 9 := (fun mask => (mask,id))

def c6732 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6732 : Upper (D 9) (R 9) [6,9,96,160,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,384] 13 (by decide) (choices 1) [1,16,64,256] r6732 c6732
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3047
  · exact u3048
  · exact u3049
  · exact u3050

def r6733 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6733 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u6733 : Upper (D 9) (R 9) [6,9,96,384,33] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,33] 13 (by decide) (choices 1) [16,64,128] r6733 c6733
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3051
  · exact u3052
  · exact u3053

def b6734 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 385 },{ cop := 4, region := 4, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7),(4,8)], upper := (rows 7 11 100 392 112 433 465 401 401), lower := (rows 7 11 100 392 112 32 64 128 256), losses := [] }

theorem u6734 : Upper (D 9) (R 9) [6,9,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6734 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6735 : Route 9 := (fun mask => (mask,id))

def c6735 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6735 : Upper (D 9) (R 9) [6,9,96,384,129] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,129] 13 (by decide) (choices 1) [16,64,256] r6735 c6735
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3054
  · exact u3055
  · exact u3056

def r6736 : Route 9 := (fun mask => (mask,id))

def c6736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u6736 : Upper (D 9) (R 9) [6,9,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384,160] 13 (by decide) (choices 1) [1,16,64,256] r6736 c6736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3057
  · exact u3058
  · exact u3059
  · exact u3060

def b6737 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 33 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 7 11 100 392 400 113 113 241 369), lower := (rows 7 11 100 392 400 32 64 128 256), losses := [] }

theorem u6737 : Upper (D 9) (R 9) [6,9,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6737 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6738 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 8, targets := 448 },{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7),(3,6),(3,7),(3,8)], upper := (rows 7 26 37 41 208 480 448 448 448), lower := (rows 7 26 37 41 208 32 64 128 256), losses := [] }

theorem u6738 : Upper (D 9) (R 9) [6,24,33,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6738 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6739 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 26 37 73 112 416 448 384 384), lower := (rows 7 26 37 73 112 32 64 128 256), losses := [] }

theorem u6739 : Upper (D 9) (R 9) [6,24,33,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6739 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6740 : Route 9 := (fun mask => (mask,id))

def c6740 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6740 : Upper (D 9) (R 9) [6,24,33,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,160] 13 (by decide) (choices 1) [64,128,256] r6740 c6740
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3061
  · exact u3062
  · exact u3063

def r6741 : Route 9 := (fun mask => (mask,id))

def c6741 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6741 : Upper (D 9) (R 9) [6,24,33,65,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,192] 13 (by decide) (choices 1) [128,256] r6741 c6741
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3064
  · exact u3065

def r6742 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6742 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6742 : Upper (D 9) (R 9) [6,24,33,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65,384] 13 (by decide) (choices 1) [64,128] r6742 c6742
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3066
  · exact u3067

def r6743 : Route 9 := (fun mask => (mask,id))

def c6743 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6743 : Upper (D 9) (R 9) [6,24,33,96,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,192] 13 (by decide) (choices 1) [1,128,256] r6743 c6743
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3068
  · exact u3069
  · exact u3070

def r6744 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6744 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6744 : Upper (D 9) (R 9) [6,24,33,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96,384] 13 (by decide) (choices 1) [1,64,128] r6744 c6744
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3071
  · exact u3072
  · exact u3073

def b6745 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 18, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(4,0),(4,5)], upper := (rows 7 26 37 200 208 289 353 417 289), lower := (rows 7 26 37 200 208 32 64 128 256), losses := [] }

theorem u6745 : Upper (D 9) (R 9) [6,24,33,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6745 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6746_256 : Upper (D 9) (R 9) [6,24,33,192,320,256] 13 :=
  permutation_upper _ _ _ [6,24,33,192,320,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3075

def r6746 : Route 9 := (fun mask => (mask,id))

def c6746 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6746 : Upper (D 9) (R 9) [6,24,33,192,320] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192,320] 13 (by decide) (choices 1) [1,128,256] r6746 c6746
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3074
  · exact u3075
  · exact m6746_256

def b6747 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 27, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,7)], upper := (rows 7 26 100 41 81 416 448 384 384), lower := (rows 7 26 100 41 81 32 64 128 256), losses := [] }

theorem u6747 : Upper (D 9) (R 9) [6,24,96,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6747 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6748 : Route 9 := (fun mask => (mask,id))

def c6748 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6748 : Upper (D 9) (R 9) [6,24,96,33,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,129] 13 (by decide) (choices 1) [64,128,256] r6748 c6748
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3076
  · exact u3077
  · exact u3078

def r6749 : Route 9 := (fun mask => (mask,id))

def c6749 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6749 : Upper (D 9) (R 9) [6,24,96,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,192] 13 (by decide) (choices 1) [1,128,256] r6749 c6749
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3079
  · exact u3080
  · exact u3081

def r6750 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6750 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6750 : Upper (D 9) (R 9) [6,24,96,33,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33,384] 13 (by decide) (choices 1) [1,64,128] r6750 c6750
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3082
  · exact u3083
  · exact u3084

def b6751 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 385 },{ cop := 3, region := 4, targets := 129 }], pairs := [(2,0),(2,7),(3,0),(3,7),(3,8)], upper := (rows 7 26 100 104 145 417 449 385 385), lower := (rows 7 26 100 104 145 32 64 128 256), losses := [] }

theorem u6751 : Upper (D 9) (R 9) [6,24,96,96,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6752 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 8, targets := 385 },{ cop := 3, region := 4, targets := 129 }], pairs := [(2,0),(2,7),(3,0),(3,7),(3,8)], upper := (rows 7 26 100 104 400 417 449 385 385), lower := (rows 7 26 100 104 400 32 64 128 256), losses := [] }

theorem u6752 : Upper (D 9) (R 9) [6,24,96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6752 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6753 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 18, targets := 352 }], pairs := [(1,5),(1,6),(1,8),(4,5),(4,6)], upper := (rows 7 26 100 137 145 352 352 480 352), lower := (rows 7 26 100 137 145 32 64 128 256), losses := [] }

theorem u6753 : Upper (D 9) (R 9) [6,24,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6753 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6754 : Route 9 := (fun mask => (mask,id))

def c6754 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6754 : Upper (D 9) (R 9) [6,24,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,160] 13 (by decide) (choices 1) [1,64,256] r6754 c6754
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3085
  · exact u3086
  · exact u3087

theorem m6755_256 : Upper (D 9) (R 9) [6,24,96,129,257,256] 13 :=
  permutation_upper _ _ _ [6,24,96,129,257,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3089

def r6755 : Route 9 := (fun mask => (mask,id))

def c6755 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6755 : Upper (D 9) (R 9) [6,24,96,129,257] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,257] 13 (by decide) (choices 1) [64,128,256] r6755 c6755
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3088
  · exact u3089
  · exact m6755_256

def r6756 : Route 9 := (fun mask => (mask,id))

def c6756 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6756 : Upper (D 9) (R 9) [6,24,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,288] 13 (by decide) (choices 1) [1,64,128,256] r6756 c6756
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3090
  · exact u3091
  · exact u3092
  · exact u3093

def r6757 : Route 9 := (fun mask => (mask,id))

def c6757 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6757 : Upper (D 9) (R 9) [6,24,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129,384] 13 (by decide) (choices 1) [1,64,256] r6757 c6757
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3094
  · exact u3095
  · exact u3096

def r6758 : Route 9 := (fun mask => (mask,id))

def c6758 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6758 : Upper (D 9) (R 9) [6,24,96,160,192] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,192] 13 (by decide) (choices 1) [1,256] r6758 c6758
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3097
  · exact u3098

def r6759 : Route 9 := (fun mask => (mask,id))

def c6759 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6759 : Upper (D 9) (R 9) [6,24,96,160,320] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,320] 13 (by decide) (choices 1) [1,128,256] r6759 c6759
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3099
  · exact u3100
  · exact u3101

def r6760 : Route 9 := (fun mask => (mask,id))

def c6760 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u6760 : Upper (D 9) (R 9) [6,24,96,160,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,160,384] 13 (by decide) (choices 1) [1,64,256] r6760 c6760
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3102
  · exact u3103
  · exact u3104

def b6761 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 18, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(4,0),(4,5)], upper := (rows 7 26 100 392 400 97 97 225 353), lower := (rows 7 26 100 392 400 32 64 128 256), losses := [] }

theorem u6761 : Upper (D 9) (R 9) [6,24,96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6761 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6762 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 },{ cop := 2, region := 419, targets := 64 }], pairs := [(0,5),(0,6),(2,5),(3,0),(4,0)], upper := (rows 7 35 69 56 88 416 448 384 384), lower := (rows 7 35 69 56 88 32 64 128 256), losses := [] }

theorem u6762 : Upper (D 9) (R 9) [6,33,65,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6762 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6763 : PairBound 9 := { available := 448, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 1, region := 453, targets := 32 },{ cop := 3, region := 464, targets := 32 }], pairs := [(0,5),(2,5),(3,0),(4,0),(4,5)], upper := (rows 7 35 69 56 152 480 448 448 448), lower := (rows 7 35 69 56 152 32 64 128 256), losses := [] }

theorem u6763 : Upper (D 9) (R 9) [6,33,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6763 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6764 : Route 9 := (fun mask => (mask,id))

def c6764 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6764 : Upper (D 9) (R 9) [6,33,65,48,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,192] 13 (by decide) (choices 1) [8,128,256] r6764 c6764
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3105
  · exact u3106
  · exact u3107

def r6765 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c6765 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u6765 : Upper (D 9) (R 9) [6,33,65,48,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,48,384] 13 (by decide) (choices 1) [8,64,128] r6765 c6765
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3108
  · exact u3109
  · exact u3110

def b6766 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 104 152 432 464 400 400), lower := (rows 7 35 69 104 152 32 64 128 256), losses := [] }

theorem u6766 : Upper (D 9) (R 9) [6,33,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6766 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6767 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 69 104 400 440 472 408 408), lower := (rows 7 35 69 104 400 32 64 128 256), losses := [] }

theorem u6767 : Upper (D 9) (R 9) [6,33,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6767 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6768 : PairBound 9 := { available := 352, camps := [{ cop := 7, region := 24, targets := 352 }], pairs := [(3,5),(3,6),(3,8),(4,5),(4,6)], upper := (rows 7 35 69 152 152 352 352 480 352), lower := (rows 7 35 69 152 152 32 64 128 256), losses := [] }

theorem u6768 : Upper (D 9) (R 9) [6,33,65,144,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6768 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6769 : PairBound 9 := { available := 328, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 0, region := 504, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,0)], upper := (rows 7 35 69 152 176 360 328 456 328), lower := (rows 7 35 69 152 176 32 64 128 256), losses := [] }

theorem u6769 : Upper (D 9) (R 9) [6,33,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6769 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m6770_256 : Upper (D 9) (R 9) [6,33,65,144,264,256] 13 :=
  permutation_upper _ _ _ [6,33,65,144,264,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3112

def r6770 : Route 9 := (fun mask => (mask,id))

def c6770 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6770 : Upper (D 9) (R 9) [6,33,65,144,264] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,264] 13 (by decide) (choices 1) [64,128,256] r6770 c6770
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3111
  · exact u3112
  · exact m6770_256

def r6771 : Route 9 := (fun mask => (mask,id))

def c6771 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | _ => 0)

theorem u6771 : Upper (D 9) (R 9) [6,33,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,33,65,144,288] 13 (by decide) (choices 1) [8,64,128,256] r6771 c6771
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3113
  · exact u3114
  · exact u3115
  · exact u3116

def b6772 : PairBound 9 := { available := 360, camps := [{ cop := 3, region := 359, targets := 128 },{ cop := 4, region := 8, targets := 96 }], pairs := [(0,7),(1,7),(2,7),(3,5),(3,6)], upper := (rows 7 35 69 152 400 360 360 488 360), lower := (rows 7 35 69 152 400 32 64 128 256), losses := [] }

theorem u6772 : Upper (D 9) (R 9) [6,33,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6772 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6773 : Route 9 := (fun mask => (mask,id))

def c6773 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u6773 : Upper (D 9) (R 9) [6,33,65,160,192] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,192] 13 (by decide) (choices 1) [8,16,256] r6773 c6773
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3117
  · exact u3118
  · exact u3119

def r6774 : Route 9 := (fun mask => (mask,id))

def c6774 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | _ => 0)

theorem u6774 : Upper (D 9) (R 9) [6,33,65,160,320] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,320] 13 (by decide) (choices 1) [8,16,128,256] r6774 c6774
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3120
  · exact u3121
  · exact u3122
  · exact u3123

def r6775 : Route 9 := (fun mask => (mask,id))

def c6775 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u6775 : Upper (D 9) (R 9) [6,33,65,160,384] 13 := by
  apply FastRouting.sound _ _ [6,33,65,160,384] 13 (by decide) (choices 1) [8,16,64,256] r6775 c6775
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3124
  · exact u3125
  · exact u3126
  · exact u3127

def b6776 : PairBound 9 := { available := 120, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 3, region := 16, targets := 96 },{ cop := 4, region := 8, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,5),(4,6)], upper := (rows 7 35 69 392 400 120 120 248 376), lower := (rows 7 35 69 392 400 32 64 128 256), losses := [] }

theorem u6776 : Upper (D 9) (R 9) [6,33,65,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6776 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b6777 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 15, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(2,7)], upper := (rows 7 35 76 25 112 416 448 384 384), lower := (rows 7 35 76 25 112 32 64 128 256), losses := [] }

theorem u6777 : Upper (D 9) (R 9) [6,33,72,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b6777 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r6778 : Route 9 := (fun mask => (mask,id))

def c6778 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u6778 : Upper (D 9) (R 9) [6,33,72,17,160] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,160] 13 (by decide) (choices 1) [64,128,256] r6778 c6778
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u3128
  · exact u3129
  · exact u3130

def r6779 : Route 9 := (fun mask => (mask,id))

def c6779 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u6779 : Upper (D 9) (R 9) [6,33,72,17,192] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17,192] 13 (by decide) (choices 1) [128,256] r6779 c6779
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u3131
  · exact u3132

#print axioms u6779
end Delivery.IrregularNine14.P09
