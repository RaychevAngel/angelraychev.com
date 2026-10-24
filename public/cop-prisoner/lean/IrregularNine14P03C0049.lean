import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0015

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b2940 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 28 145 480 480 480 480), lower := (rows 35 67 13 28 145 32 64 128 256), losses := [] }

theorem u2940 : Upper (D 3) (R 3) [34,65,9,20,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2940
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2941 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 28 176 481 449 449 449), lower := (rows 35 67 13 28 176 32 64 128 256), losses := [] }

theorem u2941 : Upper (D 3) (R 3) [34,65,9,20,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2941
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2942 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 28 208 417 481 417 417), lower := (rows 35 67 13 28 208 32 64 128 256), losses := [] }

theorem u2942 : Upper (D 3) (R 3) [34,65,9,20,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2942
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2943 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 28 273 224 224 224 480), lower := (rows 35 67 13 28 273 32 64 128 256), losses := [] }

theorem u2943 : Upper (D 3) (R 3) [34,65,9,20,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2943
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2944 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 28 304 225 193 193 449), lower := (rows 35 67 13 28 304 32 64 128 256), losses := [] }

theorem u2944 : Upper (D 3) (R 3) [34,65,9,20,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2944
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2945 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 28 336 161 225 161 417), lower := (rows 35 67 13 28 336 32 64 128 256), losses := [] }

theorem u2945 : Upper (D 3) (R 3) [34,65,9,20,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2945
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r2946 : Route 9 := (fun mask => (mask,id))

def c2946 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u2946 : Upper (D 3) (R 3) [34,65,9,20,384] 13 := by
  apply FastRouting.sound _ _ [34,65,9,20,384] 13 (by decide) (choices 1) [1,64,128] r2946 c2946
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u948
  · exact u949
  · exact u950

def b2947 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 84 432 464 400 400), lower := (rows 35 67 13 41 84 32 64 128 256), losses := [] }

theorem u2947 : Upper (D 3) (R 3) [34,65,9,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2947
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2948 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 148 496 464 464 464), lower := (rows 35 67 13 41 148 32 64 128 256), losses := [] }

theorem u2948 : Upper (D 3) (R 3) [34,65,9,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2948
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2949 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 208 436 468 404 404), lower := (rows 35 67 13 41 208 32 64 128 256), losses := [] }

theorem u2949 : Upper (D 3) (R 3) [34,65,9,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2949
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2950 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 276 240 208 208 464), lower := (rows 35 67 13 41 276 32 64 128 256), losses := [] }

theorem u2950 : Upper (D 3) (R 3) [34,65,9,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2950
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2951 : PairBound 9 := { available := 148, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 336 180 212 148 404), lower := (rows 35 67 13 41 336 32 64 128 256), losses := [] }

theorem u2951 : Upper (D 3) (R 3) [34,65,9,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2951
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2952 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 41 400 244 212 212 468), lower := (rows 35 67 13 41 400 32 64 128 256), losses := [] }

theorem u2952 : Upper (D 3) (R 3) [34,65,9,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2952
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2953 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 145 496 464 464 464), lower := (rows 35 67 13 44 145 32 64 128 256), losses := [] }

theorem u2953 : Upper (D 3) (R 3) [34,65,9,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2953
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2954 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 208 433 465 401 401), lower := (rows 35 67 13 44 208 32 64 128 256), losses := [] }

theorem u2954 : Upper (D 3) (R 3) [34,65,9,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2954
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2955 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 273 240 208 208 464), lower := (rows 35 67 13 44 273 32 64 128 256), losses := [] }

theorem u2955 : Upper (D 3) (R 3) [34,65,9,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2955
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2956 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 336 177 209 145 401), lower := (rows 35 67 13 44 336 32 64 128 256), losses := [] }

theorem u2956 : Upper (D 3) (R 3) [34,65,9,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2956
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2957 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 13 44 400 241 209 209 465), lower := (rows 35 67 13 44 400 32 64 128 256), losses := [] }

theorem u2957 : Upper (D 3) (R 3) [34,65,9,36,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2957
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2958 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 84 417 449 385 385), lower := (rows 35 67 13 56 84 32 64 128 256), losses := [] }

theorem u2958 : Upper (D 3) (R 3) [34,65,9,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2958
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2959 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 145 484 452 452 452), lower := (rows 35 67 13 56 145 32 64 128 256), losses := [] }

theorem u2959 : Upper (D 3) (R 3) [34,65,9,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2959
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2960 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 148 481 449 449 449), lower := (rows 35 67 13 56 148 32 64 128 256), losses := [] }

theorem u2960 : Upper (D 3) (R 3) [34,65,9,48,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2960
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2961 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 208 421 453 389 389), lower := (rows 35 67 13 56 208 32 64 128 256), losses := [] }

theorem u2961 : Upper (D 3) (R 3) [34,65,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2961
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2962 : PairBound 9 := { available := 196, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 273 228 196 196 452), lower := (rows 35 67 13 56 273 32 64 128 256), losses := [] }

theorem u2962 : Upper (D 3) (R 3) [34,65,9,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2962
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2963 : PairBound 9 := { available := 193, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 276 225 193 193 449), lower := (rows 35 67 13 56 276 32 64 128 256), losses := [] }

theorem u2963 : Upper (D 3) (R 3) [34,65,9,48,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2963
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2964 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 336 165 197 133 389), lower := (rows 35 67 13 56 336 32 64 128 256), losses := [] }

theorem u2964 : Upper (D 3) (R 3) [34,65,9,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2964
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2965 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 56 400 229 197 197 453), lower := (rows 35 67 13 56 400 32 64 128 256), losses := [] }

theorem u2965 : Upper (D 3) (R 3) [34,65,9,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2965
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2966 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 52 432 464 400 400), lower := (rows 35 67 13 73 52 32 64 128 256), losses := [] }

theorem u2966 : Upper (D 3) (R 3) [34,65,9,65,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2966
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2967 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 148 432 496 432 432), lower := (rows 35 67 13 73 148 32 64 128 256), losses := [] }

theorem u2967 : Upper (D 3) (R 3) [34,65,9,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2967
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2968 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 176 436 468 404 404), lower := (rows 35 67 13 73 176 32 64 128 256), losses := [] }

theorem u2968 : Upper (D 3) (R 3) [34,65,9,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2968
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2969 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 276 176 240 176 432), lower := (rows 35 67 13 73 276 32 64 128 256), losses := [] }

theorem u2969 : Upper (D 3) (R 3) [34,65,9,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2969
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2970 : PairBound 9 := { available := 148, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 304 180 212 148 404), lower := (rows 35 67 13 73 304 32 64 128 256), losses := [] }

theorem u2970 : Upper (D 3) (R 3) [34,65,9,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2970
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2971 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 73 400 180 244 180 436), lower := (rows 35 67 13 73 400 32 64 128 256), losses := [] }

theorem u2971 : Upper (D 3) (R 3) [34,65,9,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2971
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2972 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 145 432 496 432 432), lower := (rows 35 67 13 76 145 32 64 128 256), losses := [] }

theorem u2972 : Upper (D 3) (R 3) [34,65,9,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2972
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2973 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 176 433 465 401 401), lower := (rows 35 67 13 76 176 32 64 128 256), losses := [] }

theorem u2973 : Upper (D 3) (R 3) [34,65,9,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2973
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2974 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 273 176 240 176 432), lower := (rows 35 67 13 76 273 32 64 128 256), losses := [] }

theorem u2974 : Upper (D 3) (R 3) [34,65,9,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2974
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2975 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 304 177 209 145 401), lower := (rows 35 67 13 76 304 32 64 128 256), losses := [] }

theorem u2975 : Upper (D 3) (R 3) [34,65,9,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2975
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2976 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 76 400 177 241 177 433), lower := (rows 35 67 13 76 400 32 64 128 256), losses := [] }

theorem u2976 : Upper (D 3) (R 3) [34,65,9,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2976
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2977 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 88 52 417 449 385 385), lower := (rows 35 67 13 88 52 32 64 128 256), losses := [] }

theorem u2977 : Upper (D 3) (R 3) [34,65,9,80,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2977
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2978 : PairBound 9 := { available := 420, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 88 145 420 484 420 420), lower := (rows 35 67 13 88 145 32 64 128 256), losses := [] }

theorem u2978 : Upper (D 3) (R 3) [34,65,9,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2978
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2979 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 88 148 417 481 417 417), lower := (rows 35 67 13 88 148 32 64 128 256), losses := [] }

theorem u2979 : Upper (D 3) (R 3) [34,65,9,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2979
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2980 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 88 176 421 453 389 389), lower := (rows 35 67 13 88 176 32 64 128 256), losses := [] }

theorem u2980 : Upper (D 3) (R 3) [34,65,9,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2980
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2981 : PairBound 9 := { available := 164, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 88 273 164 228 164 420), lower := (rows 35 67 13 88 273 32 64 128 256), losses := [] }

theorem u2981 : Upper (D 3) (R 3) [34,65,9,80,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2981
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2982 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 88 276 161 225 161 417), lower := (rows 35 67 13 88 276 32 64 128 256), losses := [] }

theorem u2982 : Upper (D 3) (R 3) [34,65,9,80,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2982
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2983 : PairBound 9 := { available := 133, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 88 304 165 197 133 389), lower := (rows 35 67 13 88 304 32 64 128 256), losses := [] }

theorem u2983 : Upper (D 3) (R 3) [34,65,9,80,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2983
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2984 : PairBound 9 := { available := 165, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 88 400 165 229 165 421), lower := (rows 35 67 13 88 400 32 64 128 256), losses := [] }

theorem u2984 : Upper (D 3) (R 3) [34,65,9,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2984
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2985 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 145 436 468 404 404), lower := (rows 35 67 13 104 145 32 64 128 256), losses := [] }

theorem u2985 : Upper (D 3) (R 3) [34,65,9,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2985
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2986 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 148 433 465 401 401), lower := (rows 35 67 13 104 148 32 64 128 256), losses := [] }

theorem u2986 : Upper (D 3) (R 3) [34,65,9,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2986
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2987 : PairBound 9 := { available := 148, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 273 180 212 148 404), lower := (rows 35 67 13 104 273 32 64 128 256), losses := [] }

theorem u2987 : Upper (D 3) (R 3) [34,65,9,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2987
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2988 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 276 177 209 145 401), lower := (rows 35 67 13 104 276 32 64 128 256), losses := [] }

theorem u2988 : Upper (D 3) (R 3) [34,65,9,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2988
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2989 : PairBound 9 := { available := 149, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 104 400 181 213 149 405), lower := (rows 35 67 13 104 400 32 64 128 256), losses := [] }

theorem u2989 : Upper (D 3) (R 3) [34,65,9,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2989
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2990 : PairBound 9 := { available := 464, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 52 496 464 464 464), lower := (rows 35 67 13 137 52 32 64 128 256), losses := [] }

theorem u2990 : Upper (D 3) (R 3) [34,65,9,129,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2990
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2991 : PairBound 9 := { available := 432, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 84 432 496 432 432), lower := (rows 35 67 13 137 84 32 64 128 256), losses := [] }

theorem u2991 : Upper (D 3) (R 3) [34,65,9,129,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2991
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2992 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 148 368 368 496 368), lower := (rows 35 67 13 137 148 32 64 128 256), losses := [] }

theorem u2992 : Upper (D 3) (R 3) [34,65,9,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2992
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2993 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 176 372 340 468 340), lower := (rows 35 67 13 137 176 32 64 128 256), losses := [] }

theorem u2993 : Upper (D 3) (R 3) [34,65,9,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2993
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2994 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 208 308 372 436 308), lower := (rows 35 67 13 137 208 32 64 128 256), losses := [] }

theorem u2994 : Upper (D 3) (R 3) [34,65,9,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2994
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2995 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 276 240 240 240 496), lower := (rows 35 67 13 137 276 32 64 128 256), losses := [] }

theorem u2995 : Upper (D 3) (R 3) [34,65,9,129,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2995
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2996 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 304 244 212 212 468), lower := (rows 35 67 13 137 304 32 64 128 256), losses := [] }

theorem u2996 : Upper (D 3) (R 3) [34,65,9,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2996
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2997 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 336 180 244 180 436), lower := (rows 35 67 13 137 336 32 64 128 256), losses := [] }

theorem u2997 : Upper (D 3) (R 3) [34,65,9,129,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2997
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2998 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 137 400 116 116 244 372), lower := (rows 35 67 13 137 400 32 64 128 256), losses := [] }

theorem u2998 : Upper (D 3) (R 3) [34,65,9,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2998
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b2999 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 140 49 496 464 464 464), lower := (rows 35 67 13 140 49 32 64 128 256), losses := [] }

theorem u2999 : Upper (D 3) (R 3) [34,65,9,132,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b2999
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u2999
end Delivery.IrregularNine14.P03
