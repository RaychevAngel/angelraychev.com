import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0011

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 196 266 48 242 210 210 466), lower := (rows 53 11 196 266 48 32 64 128 256), losses := [] }

theorem u3060 : Upper (D 1) (R 1) [52,9,192,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3060
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 196 266 80 178 242 178 434), lower := (rows 53 11 196 266 80 32 64 128 256), losses := [] }

theorem u3061 : Upper (D 1) (R 1) [52,9,192,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3061
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3062 : Route 9 := (fun mask => (mask,id))

def c3062 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3062 : Upper (D 1) (R 1) [52,9,192,320,2] 13 := by
  apply FastRouting.sound _ _ [52,9,192,320,2] 13 (by decide) (choices 1) [2,16,128] r3062 c3062
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688

def b3063 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 196 328 48 178 210 146 402), lower := (rows 53 11 196 328 48 32 64 128 256), losses := [] }

theorem u3063 : Upper (D 1) (R 1) [52,9,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3063
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3064 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 11 196 328 144 50 114 178 306), lower := (rows 53 11 196 328 144 32 64 128 256), losses := [] }

theorem u3064 : Upper (D 1) (R 1) [52,9,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3064
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 11 262 200 18 240 240 240 496), lower := (rows 53 11 262 200 18 32 64 128 256), losses := [] }

theorem u3065 : Upper (D 1) (R 1) [52,9,258,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3065
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 262 200 48 242 210 210 466), lower := (rows 53 11 262 200 48 32 64 128 256), losses := [] }

theorem u3066 : Upper (D 1) (R 1) [52,9,258,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3066
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3067_2 : Upper (D 1) (R 1) [52,9,258,192,64,2] 13 :=
  permutation_upper _ _ _ [52,9,258,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u689

theorem m3067_16 : Upper (D 1) (R 1) [52,9,258,192,64,16] 13 :=
  permutation_upper _ _ _ [52,9,258,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u690

def r3067 : Route 9 := (fun mask => (mask,id))

def c3067 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3067 : Upper (D 1) (R 1) [52,9,258,192,64] 13 := by
  apply FastRouting.sound _ _ [52,9,258,192,64] 13 (by decide) (choices 1) [2,16,128] r3067 c3067
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3067_2
  · exact m3067_16
  · exact u691

def b3068 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 324 74 18 176 240 176 432), lower := (rows 53 11 324 74 18 32 64 128 256), losses := [] }

theorem u3068 : Upper (D 1) (R 1) [52,9,320,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3068
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3069 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 74 48 178 210 146 402), lower := (rows 53 11 324 74 48 32 64 128 256), losses := [] }

theorem u3069 : Upper (D 1) (R 1) [52,9,320,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3069
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3070_2 : Upper (D 1) (R 1) [52,9,320,66,128,2] 13 :=
  permutation_upper _ _ _ [52,9,320,66,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u692

theorem m3070_16 : Upper (D 1) (R 1) [52,9,320,66,128,16] 13 :=
  permutation_upper _ _ _ [52,9,320,66,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u693

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3070 : Upper (D 1) (R 1) [52,9,320,66,128] 13 := by
  apply FastRouting.sound _ _ [52,9,320,66,128] 13 (by decide) (choices 1) [2,16,128] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3070_2
  · exact m3070_16
  · exact u694

def b3071 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 485, targets := 2 }], pairs := [(0,1)], upper := (rows 53 11 324 138 18 240 240 240 496), lower := (rows 53 11 324 138 18 32 64 128 256), losses := [] }

theorem u3071 : Upper (D 1) (R 1) [52,9,320,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3071
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3072 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 138 48 242 210 210 466), lower := (rows 53 11 324 138 48 32 64 128 256), losses := [] }

theorem u3072 : Upper (D 1) (R 1) [52,9,320,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3072
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3073 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 138, targets := 64 }], pairs := [(1,6)], upper := (rows 53 11 324 138 80 178 242 178 434), lower := (rows 53 11 324 138 80 32 64 128 256), losses := [] }

theorem u3073 : Upper (D 1) (R 1) [52,9,320,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3073
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3074_2 : Upper (D 1) (R 1) [52,9,320,130,128,2] 13 :=
  permutation_upper _ _ _ [52,9,320,130,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u695

theorem m3074_16 : Upper (D 1) (R 1) [52,9,320,130,128,16] 13 :=
  permutation_upper _ _ _ [52,9,320,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u696

theorem m3074_64 : Upper (D 1) (R 1) [52,9,320,130,128,64] 13 :=
  permutation_upper _ _ _ [52,9,320,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u697

def r3074 : Route 9 := (fun mask => (mask,id))

def c3074 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3074 : Upper (D 1) (R 1) [52,9,320,130,128] 13 := by
  apply FastRouting.sound _ _ [52,9,320,130,128] 13 (by decide) (choices 1) [2,16,64] r3074 c3074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3074_2
  · exact m3074_16
  · exact m3074_64

def r3075 : Route 9 := (fun mask => (mask,id))

def c3075 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3075 : Upper (D 1) (R 1) [52,9,320,192,2] 13 := by
  apply FastRouting.sound _ _ [52,9,320,192,2] 13 (by decide) (choices 1) [2,16,128] r3075 c3075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u698
  · exact u699
  · exact u700

def b3076 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 11 324 200 48 178 210 146 402), lower := (rows 53 11 324 200 48 32 64 128 256), losses := [] }

theorem u3076 : Upper (D 1) (R 1) [52,9,320,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3076
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3077_2 : Upper (D 1) (R 1) [52,9,320,192,128,2] 13 :=
  permutation_upper _ _ _ [52,9,320,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u700

theorem m3077_16 : Upper (D 1) (R 1) [52,9,320,192,128,16] 13 :=
  permutation_upper _ _ _ [52,9,320,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u701

def r3077 : Route 9 := (fun mask => (mask,id))

def c3077 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3077 : Upper (D 1) (R 1) [52,9,320,192,128] 13 := by
  apply FastRouting.sound _ _ [52,9,320,192,128] 13 (by decide) (choices 1) [2,16] r3077 c3077
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3077_2
  · exact m3077_16

def b3078 : PairBound 9 := { available := 450, camps := [], pairs := [], upper := (rows 53 26 70 168 17 482 450 450 450), lower := (rows 53 26 70 168 17 32 64 128 256), losses := [] }

theorem u3078 : Upper (D 1) (R 1) [52,24,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3078
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 70 168 18 481 449 449 449), lower := (rows 53 26 70 168 18 32 64 128 256), losses := [] }

theorem u3079 : Upper (D 1) (R 1) [52,24,66,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3079
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 168 80 419 451 387 387), lower := (rows 53 26 70 168 80 32 64 128 256), losses := [] }

theorem u3080 : Upper (D 1) (R 1) [52,24,66,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3080
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 53 26 70 168 144 355 323 451 323), lower := (rows 53 26 70 168 144 32 64 128 256), losses := [] }

theorem u3081 : Upper (D 1) (R 1) [52,24,66,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3081
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 53 26 70 168 272 227 195 195 451), lower := (rows 53 26 70 168 272 32 64 128 256), losses := [] }

theorem u3082 : Upper (D 1) (R 1) [52,24,66,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3082
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 70 296 17 226 194 194 450), lower := (rows 53 26 70 296 17 32 64 128 256), losses := [] }

theorem u3083 : Upper (D 1) (R 1) [52,24,66,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3083
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 70 296 18 225 193 193 449), lower := (rows 53 26 70 296 18 32 64 128 256), losses := [] }

theorem u3084 : Upper (D 1) (R 1) [52,24,66,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3084
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 296 80 163 195 131 387), lower := (rows 53 26 70 296 80 32 64 128 256), losses := [] }

theorem u3085 : Upper (D 1) (R 1) [52,24,66,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3085
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3086 : Route 9 := (fun mask => (mask,id))

def c3086 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3086 : Upper (D 1) (R 1) [52,24,66,288,128] 13 := by
  apply FastRouting.sound _ _ [52,24,66,288,128] 13 (by decide) (choices 1) [1,2,64,128] r3086 c3086
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u702
  · exact u703
  · exact u704
  · exact u705

def b3087 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 26 70 392 17 226 226 226 482), lower := (rows 53 26 70 392 17 32 64 128 256), losses := [] }

theorem u3087 : Upper (D 1) (R 1) [52,24,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3087
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 70 392 18 225 225 225 481), lower := (rows 53 26 70 392 18 32 64 128 256), losses := [] }

theorem u3088 : Upper (D 1) (R 1) [52,24,66,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3088
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 70 392 48 227 195 195 451), lower := (rows 53 26 70 392 48 32 64 128 256), losses := [] }

theorem u3089 : Upper (D 1) (R 1) [52,24,66,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3089
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 70 392 80 163 227 163 419), lower := (rows 53 26 70 392 80 32 64 128 256), losses := [] }

theorem u3090 : Upper (D 1) (R 1) [52,24,66,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3090
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 101, targets := 128 }], pairs := [(0,7)], upper := (rows 53 26 70 392 144 99 99 227 355), lower := (rows 53 26 70 392 144 32 64 128 256), losses := [] }

theorem u3091 : Upper (D 1) (R 1) [52,24,66,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3091
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 418, camps := [], pairs := [], upper := (rows 53 26 196 74 17 418 482 418 418), lower := (rows 53 26 196 74 17 32 64 128 256), losses := [] }

theorem u3092 : Upper (D 1) (R 1) [52,24,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3092
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 74 18 417 481 417 417), lower := (rows 53 26 196 74 18 32 64 128 256), losses := [] }

theorem u3093 : Upper (D 1) (R 1) [52,24,192,66,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3093
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 74 48 419 451 387 387), lower := (rows 53 26 196 74 48 32 64 128 256), losses := [] }

theorem u3094 : Upper (D 1) (R 1) [52,24,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3094
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 196 74 144 291 355 419 291), lower := (rows 53 26 196 74 144 32 64 128 256), losses := [] }

theorem u3095 : Upper (D 1) (R 1) [52,24,192,66,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3095
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 26 196 74 272 163 227 163 419), lower := (rows 53 26 196 74 272 32 64 128 256), losses := [] }

theorem u3096 : Upper (D 1) (R 1) [52,24,192,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3096
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 386, camps := [], pairs := [], upper := (rows 53 26 196 104 17 418 450 386 386), lower := (rows 53 26 196 104 17 32 64 128 256), losses := [] }

theorem u3097 : Upper (D 1) (R 1) [52,24,192,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3097
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 387, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 104 18 419 451 387 387), lower := (rows 53 26 196 104 18 32 64 128 256), losses := [] }

theorem u3098 : Upper (D 1) (R 1) [52,24,192,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3098
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 196 104 144 291 323 387 259), lower := (rows 53 26 196 104 144 32 64 128 256), losses := [] }

theorem u3099 : Upper (D 1) (R 1) [52,24,192,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3099
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 53 26 196 104 272 163 195 131 387), lower := (rows 53 26 196 104 272 32 64 128 256), losses := [] }

theorem u3100 : Upper (D 1) (R 1) [52,24,192,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3100
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 26 196 266 17 226 226 226 482), lower := (rows 53 26 196 266 17 32 64 128 256), losses := [] }

theorem u3101 : Upper (D 1) (R 1) [52,24,192,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3101
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 225, camps := [{ cop := 8, region := 26, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 266 18 225 225 225 481), lower := (rows 53 26 196 266 18 32 64 128 256), losses := [] }

theorem u3102 : Upper (D 1) (R 1) [52,24,192,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3102
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 266 48 227 195 195 451), lower := (rows 53 26 196 266 48 32 64 128 256), losses := [] }

theorem u3103 : Upper (D 1) (R 1) [52,24,192,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3103
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 163, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 196 266 80 163 227 163 419), lower := (rows 53 26 196 266 80 32 64 128 256), losses := [] }

theorem u3104 : Upper (D 1) (R 1) [52,24,192,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3104
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 196 296 17 226 194 194 450), lower := (rows 53 26 196 296 17 32 64 128 256), losses := [] }

theorem u3105 : Upper (D 1) (R 1) [52,24,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3105
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 296 18 227 195 195 451), lower := (rows 53 26 196 296 18 32 64 128 256), losses := [] }

theorem u3106 : Upper (D 1) (R 1) [52,24,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3106
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 394, targets := 64 }], pairs := [(1,6)], upper := (rows 53 26 196 296 80 163 195 131 387), lower := (rows 53 26 196 296 80 32 64 128 256), losses := [] }

theorem u3107 : Upper (D 1) (R 1) [52,24,192,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3107
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 26 196 328 17 162 226 162 418), lower := (rows 53 26 196 328 17 32 64 128 256), losses := [] }

theorem u3108 : Upper (D 1) (R 1) [52,24,192,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3108
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3109 : PairBound 9 := { available := 163, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 328 18 163 227 163 419), lower := (rows 53 26 196 328 18 32 64 128 256), losses := [] }

theorem u3109 : Upper (D 1) (R 1) [52,24,192,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3109
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3110 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 196 328 48 163 195 131 387), lower := (rows 53 26 196 328 48 32 64 128 256), losses := [] }

theorem u3110 : Upper (D 1) (R 1) [52,24,192,320,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3110
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3111 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 330, targets := 128 }], pairs := [(1,7)], upper := (rows 53 26 196 328 144 35 99 163 291), lower := (rows 53 26 196 328 144 32 64 128 256), losses := [] }

theorem u3111 : Upper (D 1) (R 1) [52,24,192,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3111
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3112 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 53 26 262 104 17 226 194 194 450), lower := (rows 53 26 262 104 17 32 64 128 256), losses := [] }

theorem u3112 : Upper (D 1) (R 1) [52,24,258,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3112
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3113 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 262 104 18 225 193 193 449), lower := (rows 53 26 262 104 18 32 64 128 256), losses := [] }

theorem u3113 : Upper (D 1) (R 1) [52,24,258,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3113
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 262 104 80 163 195 131 387), lower := (rows 53 26 262 104 80 32 64 128 256), losses := [] }

theorem u3114 : Upper (D 1) (R 1) [52,24,258,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3114
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3115 : Route 9 := (fun mask => (mask,id))

def c3115 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3115 : Upper (D 1) (R 1) [52,24,258,96,128] 13 := by
  apply FastRouting.sound _ _ [52,24,258,96,128] 13 (by decide) (choices 1) [1,2,64,128] r3115 c3115
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u706
  · exact u707
  · exact u708
  · exact u709

def b3116 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 53 26 262 200 17 226 226 226 482), lower := (rows 53 26 262 200 17 32 64 128 256), losses := [] }

theorem u3116 : Upper (D 1) (R 1) [52,24,258,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3116
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3117 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 262 200 18 225 225 225 481), lower := (rows 53 26 262 200 18 32 64 128 256), losses := [] }

theorem u3117 : Upper (D 1) (R 1) [52,24,258,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3117
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 262 200 48 227 195 195 451), lower := (rows 53 26 262 200 48 32 64 128 256), losses := [] }

theorem u3118 : Upper (D 1) (R 1) [52,24,258,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3118
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 53 26 262 200 80 163 227 163 419), lower := (rows 53 26 262 200 80 32 64 128 256), losses := [] }

theorem u3119 : Upper (D 1) (R 1) [52,24,258,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3119
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P01
