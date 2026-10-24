import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0010
import IrregularNine14P01C0011

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m2940_2 : Upper (D 1) (R 1) [50,320,9,192,128,2] 13 :=
  permutation_upper _ _ _ [50,320,9,192,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u648

theorem m2940_4 : Upper (D 1) (R 1) [50,320,9,192,128,4] 13 :=
  permutation_upper _ _ _ [50,320,9,192,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u649

theorem m2940_16 : Upper (D 1) (R 1) [50,320,9,192,128,16] 13 :=
  permutation_upper _ _ _ [50,320,9,192,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u650

def r2940 : Route 9 := (fun mask => (mask,id))

def c2940 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2940 : Upper (D 1) (R 1) [50,320,9,192,128] 13 := by
  apply FastRouting.sound _ _ [50,320,9,192,128] 13 (by decide) (choices 1) [2,4,16] r2940 c2940
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2940_2
  · exact m2940_4
  · exact m2940_16

def b2941 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 322 14 137 20 240 240 240 496), lower := (rows 51 322 14 137 20 32 64 128 256), losses := [] }

theorem u2941 : Upper (D 1) (R 1) [50,320,10,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 14 137 48 244 212 212 468), lower := (rows 51 322 14 137 48 32 64 128 256), losses := [] }

theorem u2942 : Upper (D 1) (R 1) [50,320,10,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 14 137 80 180 244 180 436), lower := (rows 51 322 14 137 80 32 64 128 256), losses := [] }

theorem u2943 : Upper (D 1) (R 1) [50,320,10,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2943
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2944_4 : Upper (D 1) (R 1) [50,320,10,129,128,4] 13 :=
  permutation_upper _ _ _ [50,320,10,129,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u651

theorem m2944_16 : Upper (D 1) (R 1) [50,320,10,129,128,16] 13 :=
  permutation_upper _ _ _ [50,320,10,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u652

theorem m2944_64 : Upper (D 1) (R 1) [50,320,10,129,128,64] 13 :=
  permutation_upper _ _ _ [50,320,10,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u653

def r2944 : Route 9 := (fun mask => (mask,id))

def c2944 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2944 : Upper (D 1) (R 1) [50,320,10,129,128] 13 := by
  apply FastRouting.sound _ _ [50,320,10,129,128] 13 (by decide) (choices 1) [4,16,64] r2944 c2944
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2944_4
  · exact m2944_16
  · exact m2944_64

def b2945 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 51 322 14 140 17 240 240 240 496), lower := (rows 51 322 14 140 17 32 64 128 256), losses := [] }

theorem u2945 : Upper (D 1) (R 1) [50,320,10,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2946 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 14 140 48 241 209 209 465), lower := (rows 51 322 14 140 48 32 64 128 256), losses := [] }

theorem u2946 : Upper (D 1) (R 1) [50,320,10,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2946
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2947 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 14 140 80 177 241 177 433), lower := (rows 51 322 14 140 80 32 64 128 256), losses := [] }

theorem u2947 : Upper (D 1) (R 1) [50,320,10,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 14 140 144 113 113 241 369), lower := (rows 51 322 14 140 144 32 64 128 256), losses := [] }

theorem u2948 : Upper (D 1) (R 1) [50,320,10,132,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 51 322 14 152 17 228 228 228 484), lower := (rows 51 322 14 152 17 32 64 128 256), losses := [] }

theorem u2949 : Upper (D 1) (R 1) [50,320,10,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2949
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 322 14 152 20 225 225 225 481), lower := (rows 51 322 14 152 20 32 64 128 256), losses := [] }

theorem u2950 : Upper (D 1) (R 1) [50,320,10,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 14 152 48 229 197 197 453), lower := (rows 51 322 14 152 48 32 64 128 256), losses := [] }

theorem u2951 : Upper (D 1) (R 1) [50,320,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2951
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 14 152 80 165 229 165 421), lower := (rows 51 322 14 152 80 32 64 128 256), losses := [] }

theorem u2952 : Upper (D 1) (R 1) [50,320,10,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 14 152 144 101 101 229 357), lower := (rows 51 322 14 152 144 32 64 128 256), losses := [] }

theorem u2953 : Upper (D 1) (R 1) [50,320,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 134, camps := [], pairs := [], upper := (rows 51 322 28 104 17 166 198 134 390), lower := (rows 51 322 28 104 17 32 64 128 256), losses := [] }

theorem u2954 : Upper (D 1) (R 1) [50,320,24,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2954
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2955 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 104 18 165 197 133 389), lower := (rows 51 322 28 104 18 32 64 128 256), losses := [] }

theorem u2955 : Upper (D 1) (R 1) [50,320,24,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2956 : PairBound 9 := { available := 131, camps := [], pairs := [], upper := (rows 51 322 28 104 20 163 195 131 387), lower := (rows 51 322 28 104 20 32 64 128 256), losses := [] }

theorem u2956 : Upper (D 1) (R 1) [50,320,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2956
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r2957 : Route 9 := (fun mask => (mask,id))

def c2957 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u2957 : Upper (D 1) (R 1) [50,320,24,96,128] 13 := by
  apply FastRouting.sound _ _ [50,320,24,96,128] 13 (by decide) (choices 1) [1,2,4,128] r2957 c2957
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u654
  · exact u655
  · exact u656
  · exact u657

def b2958 : PairBound 9 := { available := 228, camps := [], pairs := [], upper := (rows 51 322 28 138 17 228 228 228 484), lower := (rows 51 322 28 138 17 32 64 128 256), losses := [] }

theorem u2958 : Upper (D 1) (R 1) [50,320,24,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 51 322 28 138 20 225 225 225 481), lower := (rows 51 322 28 138 20 32 64 128 256), losses := [] }

theorem u2959 : Upper (D 1) (R 1) [50,320,24,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2959
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 28 138 48 229 197 197 453), lower := (rows 51 322 28 138 48 32 64 128 256), losses := [] }

theorem u2960 : Upper (D 1) (R 1) [50,320,24,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2960
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 138 80 165 229 165 421), lower := (rows 51 322 28 138 80 32 64 128 256), losses := [] }

theorem u2961 : Upper (D 1) (R 1) [50,320,24,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2961
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 138 144 101 101 229 357), lower := (rows 51 322 28 138 144 32 64 128 256), losses := [] }

theorem u2962 : Upper (D 1) (R 1) [50,320,24,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2962
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 51 322 28 168 17 230 198 198 454), lower := (rows 51 322 28 168 17 32 64 128 256), losses := [] }

theorem u2963 : Upper (D 1) (R 1) [50,320,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2963
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 197, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 168 18 229 197 197 453), lower := (rows 51 322 28 168 18 32 64 128 256), losses := [] }

theorem u2964 : Upper (D 1) (R 1) [50,320,24,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2964
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 195, camps := [], pairs := [], upper := (rows 51 322 28 168 20 227 195 195 451), lower := (rows 51 322 28 168 20 32 64 128 256), losses := [] }

theorem u2965 : Upper (D 1) (R 1) [50,320,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2965
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 28 168 80 167 199 135 391), lower := (rows 51 322 28 168 80 32 64 128 256), losses := [] }

theorem u2966 : Upper (D 1) (R 1) [50,320,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2966
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 71, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 168 144 103 71 199 327), lower := (rows 51 322 28 168 144 32 64 128 256), losses := [] }

theorem u2967 : Upper (D 1) (R 1) [50,320,24,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2967
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 322 28 200 17 166 230 166 422), lower := (rows 51 322 28 200 17 32 64 128 256), losses := [] }

theorem u2968 : Upper (D 1) (R 1) [50,320,24,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2968
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 200 18 165 229 165 421), lower := (rows 51 322 28 200 18 32 64 128 256), losses := [] }

theorem u2969 : Upper (D 1) (R 1) [50,320,24,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2969
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 322 28 200 20 163 227 163 419), lower := (rows 51 322 28 200 20 32 64 128 256), losses := [] }

theorem u2970 : Upper (D 1) (R 1) [50,320,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2970
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 28 200 48 167 199 135 391), lower := (rows 51 322 28 200 48 32 64 128 256), losses := [] }

theorem u2971 : Upper (D 1) (R 1) [50,320,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2971
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 28 200 144 39 103 167 295), lower := (rows 51 322 28 200 144 32 64 128 256), losses := [] }

theorem u2972 : Upper (D 1) (R 1) [50,320,24,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 184, camps := [], pairs := [], upper := (rows 51 322 69 138 20 184 248 184 440), lower := (rows 51 322 69 138 20 32 64 128 256), losses := [] }

theorem u2973 : Upper (D 1) (R 1) [50,320,65,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2973
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 180, camps := [], pairs := [], upper := (rows 51 322 69 138 24 180 244 180 436), lower := (rows 51 322 69 138 24 32 64 128 256), losses := [] }

theorem u2974 : Upper (D 1) (R 1) [50,320,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2974
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 156, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 69 138 48 188 220 156 412), lower := (rows 51 322 69 138 48 32 64 128 256), losses := [] }

theorem u2975 : Upper (D 1) (R 1) [50,320,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2975
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2976_4 : Upper (D 1) (R 1) [50,320,65,130,128,4] 13 :=
  permutation_upper _ _ _ [50,320,65,130,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u658

theorem m2976_8 : Upper (D 1) (R 1) [50,320,65,130,128,8] 13 :=
  permutation_upper _ _ _ [50,320,65,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u659

theorem m2976_16 : Upper (D 1) (R 1) [50,320,65,130,128,16] 13 :=
  permutation_upper _ _ _ [50,320,65,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u660

def r2976 : Route 9 := (fun mask => (mask,id))

def c2976 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2976 : Upper (D 1) (R 1) [50,320,65,130,128] 13 := by
  apply FastRouting.sound _ _ [50,320,65,130,128] 13 (by decide) (choices 1) [4,8,16] r2976 c2976
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2976_4
  · exact m2976_8
  · exact m2976_16

def b2977 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 69 140 18 184 248 184 440), lower := (rows 51 322 69 140 18 32 64 128 256), losses := [] }

theorem u2977 : Upper (D 1) (R 1) [50,320,65,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2977
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 322 69 140 24 178 242 178 434), lower := (rows 51 322 69 140 24 32 64 128 256), losses := [] }

theorem u2978 : Upper (D 1) (R 1) [50,320,65,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2978
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 69 140 48 186 218 154 410), lower := (rows 51 322 69 140 48 32 64 128 256), losses := [] }

theorem u2979 : Upper (D 1) (R 1) [50,320,65,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2979
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2980_2 : Upper (D 1) (R 1) [50,320,65,132,128,2] 13 :=
  permutation_upper _ _ _ [50,320,65,132,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u661

theorem m2980_8 : Upper (D 1) (R 1) [50,320,65,132,128,8] 13 :=
  permutation_upper _ _ _ [50,320,65,132,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u662

theorem m2980_16 : Upper (D 1) (R 1) [50,320,65,132,128,16] 13 :=
  permutation_upper _ _ _ [50,320,65,132,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u663

def r2980 : Route 9 := (fun mask => (mask,id))

def c2980 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2980 : Upper (D 1) (R 1) [50,320,65,132,128] 13 := by
  apply FastRouting.sound _ _ [50,320,65,132,128] 13 (by decide) (choices 1) [2,8,16] r2980 c2980
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2980_2
  · exact m2980_8
  · exact m2980_16

def b2981 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 69 152 18 172 236 172 428), lower := (rows 51 322 69 152 18 32 64 128 256), losses := [] }

theorem u2981 : Upper (D 1) (R 1) [50,320,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2981
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 51 322 69 152 20 170 234 170 426), lower := (rows 51 322 69 152 20 32 64 128 256), losses := [] }

theorem u2982 : Upper (D 1) (R 1) [50,320,65,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 322 69 152 24 166 230 166 422), lower := (rows 51 322 69 152 24 32 64 128 256), losses := [] }

theorem u2983 : Upper (D 1) (R 1) [50,320,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 142, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 69 152 48 174 206 142 398), lower := (rows 51 322 69 152 48 32 64 128 256), losses := [] }

theorem u2984 : Upper (D 1) (R 1) [50,320,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 46, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 69 152 144 46 110 174 302), lower := (rows 51 322 69 152 144 32 64 128 256), losses := [] }

theorem u2985 : Upper (D 1) (R 1) [50,320,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 180, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 76 137 18 180 244 180 436), lower := (rows 51 322 76 137 18 32 64 128 256), losses := [] }

theorem u2986 : Upper (D 1) (R 1) [50,320,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2987 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 51 322 76 137 20 178 242 178 434), lower := (rows 51 322 76 137 20 32 64 128 256), losses := [] }

theorem u2987 : Upper (D 1) (R 1) [50,320,72,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2987
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 150, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 137 48 182 214 150 406), lower := (rows 51 322 76 137 48 32 64 128 256), losses := [] }

theorem u2988 : Upper (D 1) (R 1) [50,320,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2988
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2989_2 : Upper (D 1) (R 1) [50,320,72,129,128,2] 13 :=
  permutation_upper _ _ _ [50,320,72,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u664

theorem m2989_4 : Upper (D 1) (R 1) [50,320,72,129,128,4] 13 :=
  permutation_upper _ _ _ [50,320,72,129,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u665

theorem m2989_16 : Upper (D 1) (R 1) [50,320,72,129,128,16] 13 :=
  permutation_upper _ _ _ [50,320,72,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u666

def r2989 : Route 9 := (fun mask => (mask,id))

def c2989 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2989 : Upper (D 1) (R 1) [50,320,72,129,128] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129,128] 13 (by decide) (choices 1) [2,4,16] r2989 c2989
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2989_2
  · exact m2989_4
  · exact m2989_16

def b2990 : PairBound 9 := { available := 180, camps := [], pairs := [], upper := (rows 51 322 76 138 17 180 244 180 436), lower := (rows 51 322 76 138 17 32 64 128 256), losses := [] }

theorem u2990 : Upper (D 1) (R 1) [50,320,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2990
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 322 76 138 20 177 241 177 433), lower := (rows 51 322 76 138 20 32 64 128 256), losses := [] }

theorem u2991 : Upper (D 1) (R 1) [50,320,72,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2991
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 138 48 181 213 149 405), lower := (rows 51 322 76 138 48 32 64 128 256), losses := [] }

theorem u2992 : Upper (D 1) (R 1) [50,320,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2992
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m2993_1 : Upper (D 1) (R 1) [50,320,72,130,128,1] 13 :=
  permutation_upper _ _ _ [50,320,72,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u667

theorem m2993_4 : Upper (D 1) (R 1) [50,320,72,130,128,4] 13 :=
  permutation_upper _ _ _ [50,320,72,130,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u668

theorem m2993_16 : Upper (D 1) (R 1) [50,320,72,130,128,16] 13 :=
  permutation_upper _ _ _ [50,320,72,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u669

def r2993 : Route 9 := (fun mask => (mask,id))

def c2993 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2993 : Upper (D 1) (R 1) [50,320,72,130,128] 13 := by
  apply FastRouting.sound _ _ [50,320,72,130,128] 13 (by decide) (choices 1) [1,4,16] r2993 c2993
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m2993_1
  · exact m2993_4
  · exact m2993_16

def b2994 : PairBound 9 := { available := 166, camps := [], pairs := [], upper := (rows 51 322 76 152 17 166 230 166 422), lower := (rows 51 322 76 152 17 32 64 128 256), losses := [] }

theorem u2994 : Upper (D 1) (R 1) [50,320,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2994
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2995 : PairBound 9 := { available := 165, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 76 152 18 165 229 165 421), lower := (rows 51 322 76 152 18 32 64 128 256), losses := [] }

theorem u2995 : Upper (D 1) (R 1) [50,320,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 51 322 76 152 20 163 227 163 419), lower := (rows 51 322 76 152 20 32 64 128 256), losses := [] }

theorem u2996 : Upper (D 1) (R 1) [50,320,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2996
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 135, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 152 48 167 199 135 391), lower := (rows 51 322 76 152 48 32 64 128 256), losses := [] }

theorem u2997 : Upper (D 1) (R 1) [50,320,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2997
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 39, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 76 152 144 39 103 167 295), lower := (rows 51 322 76 152 144 32 64 128 256), losses := [] }

theorem u2998 : Upper (D 1) (R 1) [50,320,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2998
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 172, camps := [{ cop := 0, region := 204, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 84 137 18 172 236 172 428), lower := (rows 51 322 84 137 18 32 64 128 256), losses := [] }

theorem u2999 : Upper (D 1) (R 1) [50,320,80,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b2999
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P01
