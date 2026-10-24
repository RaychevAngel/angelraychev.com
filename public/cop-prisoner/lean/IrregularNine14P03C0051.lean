import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0016
import IrregularNine14P03C0017

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3060 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 296 145 244 212 212 468), lower := (rows 35 67 13 296 145 32 64 128 256), losses := [] }

theorem u3060 : Upper (D 3) (R 3) [34,65,9,288,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3060
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3061 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 296 148 241 209 209 465), lower := (rows 35 67 13 296 148 32 64 128 256), losses := [] }

theorem u3061 : Upper (D 3) (R 3) [34,65,9,288,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3061
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3062 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 296 208 181 213 149 405), lower := (rows 35 67 13 296 208 32 64 128 256), losses := [] }

theorem u3062 : Upper (D 3) (R 3) [34,65,9,288,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3062
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3063 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 328 52 177 209 145 401), lower := (rows 35 67 13 328 52 32 64 128 256), losses := [] }

theorem u3063 : Upper (D 3) (R 3) [34,65,9,320,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3063
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3064 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 328 145 180 244 180 436), lower := (rows 35 67 13 328 145 32 64 128 256), losses := [] }

theorem u3064 : Upper (D 3) (R 3) [34,65,9,320,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3064
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3065 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 328 148 177 241 177 433), lower := (rows 35 67 13 328 148 32 64 128 256), losses := [] }

theorem u3065 : Upper (D 3) (R 3) [34,65,9,320,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3065
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3066 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 328 176 181 213 149 405), lower := (rows 35 67 13 328 176 32 64 128 256), losses := [] }

theorem u3066 : Upper (D 3) (R 3) [34,65,9,320,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3066
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3067 : PairBound 9 := { available := 212, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 392 49 244 212 212 468), lower := (rows 35 67 13 392 49 32 64 128 256), losses := [] }

theorem u3067 : Upper (D 3) (R 3) [34,65,9,384,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3067
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3068 : Route 9 := (fun mask => (mask,id))

def c3068 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3068 : Upper (D 3) (R 3) [34,65,9,384,36] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,36] 13 (by decide) (choices 1) [1,16,64,128] r3068 c3068
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u989
  · exact u990
  · exact u991
  · exact u992

def b3069 : PairBound 9 := { available := 180, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 13 392 81 180 244 180 436), lower := (rows 35 67 13 392 81 32 64 128 256), losses := [] }

theorem u3069 : Upper (D 3) (R 3) [34,65,9,384,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3069
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3070 : Route 9 := (fun mask => (mask,id))

def c3070 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3070 : Upper (D 3) (R 3) [34,65,9,384,68] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,68] 13 (by decide) (choices 1) [1,16,128] r3070 c3070
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u993
  · exact u994
  · exact u995

def b3071 : PairBound 9 := { available := 149, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 392 112 181 213 149 405), lower := (rows 35 67 13 392 112 32 64 128 256), losses := [] }

theorem u3071 : Upper (D 3) (R 3) [34,65,9,384,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3071
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3072 : Route 9 := (fun mask => (mask,id))

def c3072 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3072 : Upper (D 3) (R 3) [34,65,9,384,129] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,129] 13 (by decide) (choices 1) [4,16,64] r3072 c3072
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u996
  · exact u997
  · exact u998

def b3073 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 392 148 113 113 241 369), lower := (rows 35 67 13 392 148 32 64 128 256), losses := [] }

theorem u3073 : Upper (D 3) (R 3) [34,65,9,384,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3073
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3074 : Route 9 := (fun mask => (mask,id))

def c3074 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3074 : Upper (D 3) (R 3) [34,65,9,384,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,160] 13 (by decide) (choices 1) [1,4,16,64] r3074 c3074
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u999
  · exact u1000
  · exact u1001
  · exact u1002

def r3075 : Route 9 := (fun mask => (mask,id))

def c3075 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3075 : Upper (D 3) (R 3) [34,65,9,384,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,384,192] 13 (by decide) (choices 1) [1,4,16] r3075 c3075
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1003
  · exact u1004
  · exact u1005

def b3076 : PairBound 9 := { available := 452, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 145 484 452 452 452), lower := (rows 35 67 28 41 145 32 64 128 256), losses := [] }

theorem u3076 : Upper (D 3) (R 3) [34,65,24,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3076
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3077 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 148 481 449 449 449), lower := (rows 35 67 28 41 148 32 64 128 256), losses := [] }

theorem u3077 : Upper (D 3) (R 3) [34,65,24,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3077
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3078 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 208 421 453 389 389), lower := (rows 35 67 28 41 208 32 64 128 256), losses := [] }

theorem u3078 : Upper (D 3) (R 3) [34,65,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3078
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3079 : PairBound 9 := { available := 196, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 273 228 196 196 452), lower := (rows 35 67 28 41 273 32 64 128 256), losses := [] }

theorem u3079 : Upper (D 3) (R 3) [34,65,24,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3079
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3080 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 276 225 193 193 449), lower := (rows 35 67 28 41 276 32 64 128 256), losses := [] }

theorem u3080 : Upper (D 3) (R 3) [34,65,24,33,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3080
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3081 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 336 165 197 133 389), lower := (rows 35 67 28 41 336 32 64 128 256), losses := [] }

theorem u3081 : Upper (D 3) (R 3) [34,65,24,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3081
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3082 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 41 400 229 197 197 453), lower := (rows 35 67 28 41 400 32 64 128 256), losses := [] }

theorem u3082 : Upper (D 3) (R 3) [34,65,24,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3082
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3083 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 145 481 449 449 449), lower := (rows 35 67 28 44 145 32 64 128 256), losses := [] }

theorem u3083 : Upper (D 3) (R 3) [34,65,24,36,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3083
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3084 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 208 417 449 385 385), lower := (rows 35 67 28 44 208 32 64 128 256), losses := [] }

theorem u3084 : Upper (D 3) (R 3) [34,65,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3084
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3085 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 273 225 193 193 449), lower := (rows 35 67 28 44 273 32 64 128 256), losses := [] }

theorem u3085 : Upper (D 3) (R 3) [34,65,24,36,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3085
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3086 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 336 161 193 129 385), lower := (rows 35 67 28 44 336 32 64 128 256), losses := [] }

theorem u3086 : Upper (D 3) (R 3) [34,65,24,36,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3086
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3087 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 44 400 225 193 193 449), lower := (rows 35 67 28 44 400 32 64 128 256), losses := [] }

theorem u3087 : Upper (D 3) (R 3) [34,65,24,36,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3087
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3088 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 145 420 484 420 420), lower := (rows 35 67 28 73 145 32 64 128 256), losses := [] }

theorem u3088 : Upper (D 3) (R 3) [34,65,24,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3088
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3089 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 148 417 481 417 417), lower := (rows 35 67 28 73 148 32 64 128 256), losses := [] }

theorem u3089 : Upper (D 3) (R 3) [34,65,24,65,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3089
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3090 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 176 421 453 389 389), lower := (rows 35 67 28 73 176 32 64 128 256), losses := [] }

theorem u3090 : Upper (D 3) (R 3) [34,65,24,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3090
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3091 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 273 164 228 164 420), lower := (rows 35 67 28 73 273 32 64 128 256), losses := [] }

theorem u3091 : Upper (D 3) (R 3) [34,65,24,65,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3091
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3092 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 276 161 225 161 417), lower := (rows 35 67 28 73 276 32 64 128 256), losses := [] }

theorem u3092 : Upper (D 3) (R 3) [34,65,24,65,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3092
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3093 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 304 165 197 133 389), lower := (rows 35 67 28 73 304 32 64 128 256), losses := [] }

theorem u3093 : Upper (D 3) (R 3) [34,65,24,65,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3093
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3094 : PairBound 9 := { available := 165, camps := [{ cop := 1, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 67 28 73 400 165 229 165 421), lower := (rows 35 67 28 73 400 32 64 128 256), losses := [] }

theorem u3094 : Upper (D 3) (R 3) [34,65,24,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3094
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3095 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 145 417 481 417 417), lower := (rows 35 67 28 76 145 32 64 128 256), losses := [] }

theorem u3095 : Upper (D 3) (R 3) [34,65,24,68,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3095
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3096 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 176 417 449 385 385), lower := (rows 35 67 28 76 176 32 64 128 256), losses := [] }

theorem u3096 : Upper (D 3) (R 3) [34,65,24,68,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3096
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3097 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 273 161 225 161 417), lower := (rows 35 67 28 76 273 32 64 128 256), losses := [] }

theorem u3097 : Upper (D 3) (R 3) [34,65,24,68,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3097
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3098 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 304 161 193 129 385), lower := (rows 35 67 28 76 304 32 64 128 256), losses := [] }

theorem u3098 : Upper (D 3) (R 3) [34,65,24,68,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3098
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3099 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 76 400 161 225 161 417), lower := (rows 35 67 28 76 400 32 64 128 256), losses := [] }

theorem u3099 : Upper (D 3) (R 3) [34,65,24,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3099
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3100 : PairBound 9 := { available := 389, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 145 421 453 389 389), lower := (rows 35 67 28 104 145 32 64 128 256), losses := [] }

theorem u3100 : Upper (D 3) (R 3) [34,65,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3100
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3101 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 148 417 449 385 385), lower := (rows 35 67 28 104 148 32 64 128 256), losses := [] }

theorem u3101 : Upper (D 3) (R 3) [34,65,24,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3101
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3102 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 273 165 197 133 389), lower := (rows 35 67 28 104 273 32 64 128 256), losses := [] }

theorem u3102 : Upper (D 3) (R 3) [34,65,24,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3102
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3103 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 276 161 193 129 385), lower := (rows 35 67 28 104 276 32 64 128 256), losses := [] }

theorem u3103 : Upper (D 3) (R 3) [34,65,24,96,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3103
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3104 : PairBound 9 := { available := 133, camps := [{ cop := 3, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 104 400 165 197 133 389), lower := (rows 35 67 28 104 400 32 64 128 256), losses := [] }

theorem u3104 : Upper (D 3) (R 3) [34,65,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3104
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3105 : PairBound 9 := { available := 356, camps := [{ cop := 3, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 28 137 145 356 356 484 356), lower := (rows 35 67 28 137 145 32 64 128 256), losses := [] }

theorem u3105 : Upper (D 3) (R 3) [34,65,24,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3105
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3106 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 137 148 353 353 481 353), lower := (rows 35 67 28 137 148 32 64 128 256), losses := [] }

theorem u3106 : Upper (D 3) (R 3) [34,65,24,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3106
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3107 : PairBound 9 := { available := 325, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 176 357 325 453 325), lower := (rows 35 67 28 137 176 32 64 128 256), losses := [] }

theorem u3107 : Upper (D 3) (R 3) [34,65,24,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3107
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3108 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 208 293 357 421 293), lower := (rows 35 67 28 137 208 32 64 128 256), losses := [] }

theorem u3108 : Upper (D 3) (R 3) [34,65,24,129,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3108
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3109 : Route 9 := (fun mask => (mask,id))

def c3109 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3109 : Upper (D 3) (R 3) [34,65,24,129,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,257] 13 (by decide) (choices 1) [4,64,128] r3109 c3109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1006
  · exact u1007
  · exact u1008

def r3110 : Route 9 := (fun mask => (mask,id))

def c3110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3110 : Upper (D 3) (R 3) [34,65,24,129,260] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,260] 13 (by decide) (choices 1) [1,64,128] r3110 c3110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1009
  · exact u1010
  · exact u1011

def r3111 : Route 9 := (fun mask => (mask,id))

def c3111 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3111 : Upper (D 3) (R 3) [34,65,24,129,288] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,288] 13 (by decide) (choices 1) [1,4,64,128] r3111 c3111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1012
  · exact u1013
  · exact u1014
  · exact u1015

def r3112 : Route 9 := (fun mask => (mask,id))

def c3112 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3112 : Upper (D 3) (R 3) [34,65,24,129,320] 13 := by
  apply FastRouting.sound _ _ [34,65,24,129,320] 13 (by decide) (choices 1) [1,4,128] r3112 c3112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1016
  · exact u1017
  · exact u1018

def b3113 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 137 400 101 101 229 357), lower := (rows 35 67 28 137 400 32 64 128 256), losses := [] }

theorem u3113 : Upper (D 3) (R 3) [34,65,24,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3113
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3114 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 176 353 321 449 321), lower := (rows 35 67 28 140 176 32 64 128 256), losses := [] }

theorem u3114 : Upper (D 3) (R 3) [34,65,24,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3114
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3115 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 208 289 353 417 289), lower := (rows 35 67 28 140 208 32 64 128 256), losses := [] }

theorem u3115 : Upper (D 3) (R 3) [34,65,24,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3115
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3116 : Route 9 := (fun mask => (mask,id))

def c3116 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3116 : Upper (D 3) (R 3) [34,65,24,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,24,132,257] 13 (by decide) (choices 1) [1,64,128] r3116 c3116
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1019
  · exact u1020
  · exact u1021

def b3117 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 140 304 225 193 193 449), lower := (rows 35 67 28 140 304 32 64 128 256), losses := [] }

theorem u3117 : Upper (D 3) (R 3) [34,65,24,132,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3117
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3118 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 28 140 336 161 225 161 417), lower := (rows 35 67 28 140 336 32 64 128 256), losses := [] }

theorem u3118 : Upper (D 3) (R 3) [34,65,24,132,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3118
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3119 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 400 97 97 225 353), lower := (rows 35 67 28 140 400 32 64 128 256), losses := [] }

theorem u3119 : Upper (D 3) (R 3) [34,65,24,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3119
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3119
end Delivery.IrregularNine14.P03
