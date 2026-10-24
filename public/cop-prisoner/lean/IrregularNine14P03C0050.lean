import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0015
import IrregularNine14P03C0016

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3000 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 13 140 81 432 496 432 432), lower := (rows 35 67 13 140 81 32 64 128 256), losses := [] }

theorem u3000 : Upper (D 3) (R 3) [34,65,9,132,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3000
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3001 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 112 433 465 401 401), lower := (rows 35 67 13 140 112 32 64 128 256), losses := [] }

theorem u3001 : Upper (D 3) (R 3) [34,65,9,132,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3001
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3002 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 140 145 368 368 496 368), lower := (rows 35 67 13 140 145 32 64 128 256), losses := [] }

theorem u3002 : Upper (D 3) (R 3) [34,65,9,132,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3002
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3003 : PairBound 9 := { available := 337, camps := [{ cop := 4, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 176 369 337 465 337), lower := (rows 35 67 13 140 176 32 64 128 256), losses := [] }

theorem u3003 : Upper (D 3) (R 3) [34,65,9,132,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3003
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3004 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 291, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 208 305 369 433 305), lower := (rows 35 67 13 140 208 32 64 128 256), losses := [] }

theorem u3004 : Upper (D 3) (R 3) [34,65,9,132,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3004
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3005 : Route 9 := (fun mask => (mask,id))

def c3005 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3005 : Upper (D 3) (R 3) [34,65,9,132,257] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,257] 13 (by decide) (choices 1) [16,64,128] r3005 c3005
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u951
  · exact u952
  · exact u953

def r3006 : Route 9 := (fun mask => (mask,id))

def c3006 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3006 : Upper (D 3) (R 3) [34,65,9,132,288] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,288] 13 (by decide) (choices 1) [1,16,64,128] r3006 c3006
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u954
  · exact u955
  · exact u956
  · exact u957

def r3007 : Route 9 := (fun mask => (mask,id))

def c3007 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3007 : Upper (D 3) (R 3) [34,65,9,132,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,132,320] 13 (by decide) (choices 1) [1,16,128] r3007 c3007
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u958
  · exact u959
  · exact u960

def b3008 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 140 400 113 113 241 369), lower := (rows 35 67 13 140 400 32 64 128 256), losses := [] }

theorem u3008 : Upper (D 3) (R 3) [34,65,9,132,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3008
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3009 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 152 49 484 452 452 452), lower := (rows 35 67 13 152 49 32 64 128 256), losses := [] }

theorem u3009 : Upper (D 3) (R 3) [34,65,9,144,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3009
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3010 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 152 52 481 449 449 449), lower := (rows 35 67 13 152 52 32 64 128 256), losses := [] }

theorem u3010 : Upper (D 3) (R 3) [34,65,9,144,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3010
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3011 : PairBound 9 := { available := 420, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 13 152 81 420 484 420 420), lower := (rows 35 67 13 152 81 32 64 128 256), losses := [] }

theorem u3011 : Upper (D 3) (R 3) [34,65,9,144,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3011
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3012 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 152 84 417 481 417 417), lower := (rows 35 67 13 152 84 32 64 128 256), losses := [] }

theorem u3012 : Upper (D 3) (R 3) [34,65,9,144,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3012
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3013 : PairBound 9 := { available := 389, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 112 421 453 389 389), lower := (rows 35 67 13 152 112 32 64 128 256), losses := [] }

theorem u3013 : Upper (D 3) (R 3) [34,65,9,144,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3013
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3014 : PairBound 9 := { available := 356, camps := [{ cop := 4, region := 12, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 152 145 356 356 484 356), lower := (rows 35 67 13 152 145 32 64 128 256), losses := [] }

theorem u3014 : Upper (D 3) (R 3) [34,65,9,144,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3014
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3015 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 148 353 353 481 353), lower := (rows 35 67 13 152 148 32 64 128 256), losses := [] }

theorem u3015 : Upper (D 3) (R 3) [34,65,9,144,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3015
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3016 : PairBound 9 := { available := 325, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 176 357 325 453 325), lower := (rows 35 67 13 152 176 32 64 128 256), losses := [] }

theorem u3016 : Upper (D 3) (R 3) [34,65,9,144,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3016
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3017 : PairBound 9 := { available := 293, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 208 293 357 421 293), lower := (rows 35 67 13 152 208 32 64 128 256), losses := [] }

theorem u3017 : Upper (D 3) (R 3) [34,65,9,144,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3017
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3018 : Route 9 := (fun mask => (mask,id))

def c3018 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3018 : Upper (D 3) (R 3) [34,65,9,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,257] 13 (by decide) (choices 1) [4,64,128] r3018 c3018
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u961
  · exact u962
  · exact u963

def r3019 : Route 9 := (fun mask => (mask,id))

def c3019 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3019 : Upper (D 3) (R 3) [34,65,9,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,260] 13 (by decide) (choices 1) [1,64,128] r3019 c3019
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u964
  · exact u965
  · exact u966

def b3020 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 152 304 229 197 197 453), lower := (rows 35 67 13 152 304 32 64 128 256), losses := [] }

theorem u3020 : Upper (D 3) (R 3) [34,65,9,144,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3020
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3021 : Route 9 := (fun mask => (mask,id))

def c3021 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3021 : Upper (D 3) (R 3) [34,65,9,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,9,144,320] 13 (by decide) (choices 1) [1,4,128] r3021 c3021
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u967
  · exact u968
  · exact u969

def b3022 : PairBound 9 := { available := 101, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 152 400 101 101 229 357), lower := (rows 35 67 13 152 400 32 64 128 256), losses := [] }

theorem u3022 : Upper (D 3) (R 3) [34,65,9,144,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3022
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3023 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 84 433 465 401 401), lower := (rows 35 67 13 168 84 32 64 128 256), losses := [] }

theorem u3023 : Upper (D 3) (R 3) [34,65,9,160,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3023
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3024 : PairBound 9 := { available := 340, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 145 372 340 468 340), lower := (rows 35 67 13 168 145 32 64 128 256), losses := [] }

theorem u3024 : Upper (D 3) (R 3) [34,65,9,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3024
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3025 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 148 369 337 465 337), lower := (rows 35 67 13 168 148 32 64 128 256), losses := [] }

theorem u3025 : Upper (D 3) (R 3) [34,65,9,160,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3025
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3026 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 208 309 341 405 277), lower := (rows 35 67 13 168 208 32 64 128 256), losses := [] }

theorem u3026 : Upper (D 3) (R 3) [34,65,9,160,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3026
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3027 : PairBound 9 := { available := 212, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 273 244 212 212 468), lower := (rows 35 67 13 168 273 32 64 128 256), losses := [] }

theorem u3027 : Upper (D 3) (R 3) [34,65,9,160,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3027
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3028 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 276 241 209 209 465), lower := (rows 35 67 13 168 276 32 64 128 256), losses := [] }

theorem u3028 : Upper (D 3) (R 3) [34,65,9,160,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3028
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3029 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 336 181 213 149 405), lower := (rows 35 67 13 168 336 32 64 128 256), losses := [] }

theorem u3029 : Upper (D 3) (R 3) [34,65,9,160,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3029
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3030 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 168 400 117 85 213 341), lower := (rows 35 67 13 168 400 32 64 128 256), losses := [] }

theorem u3030 : Upper (D 3) (R 3) [34,65,9,160,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3030
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3031 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 52 433 465 401 401), lower := (rows 35 67 13 200 52 32 64 128 256), losses := [] }

theorem u3031 : Upper (D 3) (R 3) [34,65,9,192,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3031
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3032 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 145 308 372 436 308), lower := (rows 35 67 13 200 145 32 64 128 256), losses := [] }

theorem u3032 : Upper (D 3) (R 3) [34,65,9,192,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3032
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3033 : PairBound 9 := { available := 305, camps := [{ cop := 4, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 200 148 305 369 433 305), lower := (rows 35 67 13 200 148 32 64 128 256), losses := [] }

theorem u3033 : Upper (D 3) (R 3) [34,65,9,192,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3033
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3034 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 176 309 341 405 277), lower := (rows 35 67 13 200 176 32 64 128 256), losses := [] }

theorem u3034 : Upper (D 3) (R 3) [34,65,9,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3034
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3035 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 273 180 244 180 436), lower := (rows 35 67 13 200 273 32 64 128 256), losses := [] }

theorem u3035 : Upper (D 3) (R 3) [34,65,9,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3035
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3036 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 276 177 241 177 433), lower := (rows 35 67 13 200 276 32 64 128 256), losses := [] }

theorem u3036 : Upper (D 3) (R 3) [34,65,9,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3036
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3037 : PairBound 9 := { available := 149, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 304 181 213 149 405), lower := (rows 35 67 13 200 304 32 64 128 256), losses := [] }

theorem u3037 : Upper (D 3) (R 3) [34,65,9,192,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3037
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3038 : PairBound 9 := { available := 53, camps := [{ cop := 2, region := 432, targets := 64 }], pairs := [(4,6)], upper := (rows 35 67 13 200 400 53 117 181 309), lower := (rows 35 67 13 200 400 32 64 128 256), losses := [] }

theorem u3038 : Upper (D 3) (R 3) [34,65,9,192,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3038
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3039 : PairBound 9 := { available := 208, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 52 240 208 208 464), lower := (rows 35 67 13 265 52 32 64 128 256), losses := [] }

theorem u3039 : Upper (D 3) (R 3) [34,65,9,257,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3039
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3040 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 84 176 240 176 432), lower := (rows 35 67 13 265 84 32 64 128 256), losses := [] }

theorem u3040 : Upper (D 3) (R 3) [34,65,9,257,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3040
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3041 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 148 240 240 240 496), lower := (rows 35 67 13 265 148 32 64 128 256), losses := [] }

theorem u3041 : Upper (D 3) (R 3) [34,65,9,257,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3041
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3042 : PairBound 9 := { available := 212, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 176 244 212 212 468), lower := (rows 35 67 13 265 176 32 64 128 256), losses := [] }

theorem u3042 : Upper (D 3) (R 3) [34,65,9,257,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3042
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3043 : PairBound 9 := { available := 180, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 265 208 180 244 180 436), lower := (rows 35 67 13 265 208 32 64 128 256), losses := [] }

theorem u3043 : Upper (D 3) (R 3) [34,65,9,257,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3043
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3044 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 268 49 240 208 208 464), lower := (rows 35 67 13 268 49 32 64 128 256), losses := [] }

theorem u3044 : Upper (D 3) (R 3) [34,65,9,260,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3044
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3045 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 13 268 81 176 240 176 432), lower := (rows 35 67 13 268 81 32 64 128 256), losses := [] }

theorem u3045 : Upper (D 3) (R 3) [34,65,9,260,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3045
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3046 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 268 112 177 209 145 401), lower := (rows 35 67 13 268 112 32 64 128 256), losses := [] }

theorem u3046 : Upper (D 3) (R 3) [34,65,9,260,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3046
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3047 : Route 9 := (fun mask => (mask,id))

def c3047 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3047 : Upper (D 3) (R 3) [34,65,9,260,129] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,129] 13 (by decide) (choices 1) [16,64,128] r3047 c3047
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u970
  · exact u971
  · exact u972

def r3048 : Route 9 := (fun mask => (mask,id))

def c3048 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u3048 : Upper (D 3) (R 3) [34,65,9,260,160] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,160] 13 (by decide) (choices 1) [1,16,64,128] r3048 c3048
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u973
  · exact u974
  · exact u975
  · exact u976

def r3049 : Route 9 := (fun mask => (mask,id))

def c3049 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3049 : Upper (D 3) (R 3) [34,65,9,260,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,260,192] 13 (by decide) (choices 1) [1,16,128] r3049 c3049
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u977
  · exact u978
  · exact u979

def b3050 : PairBound 9 := { available := 196, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 280 49 228 196 196 452), lower := (rows 35 67 13 280 49 32 64 128 256), losses := [] }

theorem u3050 : Upper (D 3) (R 3) [34,65,9,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3050
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3051 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 280 52 225 193 193 449), lower := (rows 35 67 13 280 52 32 64 128 256), losses := [] }

theorem u3051 : Upper (D 3) (R 3) [34,65,9,272,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3051
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3052 : PairBound 9 := { available := 164, camps := [{ cop := 1, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 35 67 13 280 81 164 228 164 420), lower := (rows 35 67 13 280 81 32 64 128 256), losses := [] }

theorem u3052 : Upper (D 3) (R 3) [34,65,9,272,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3052
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3053 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 67 13 280 84 161 225 161 417), lower := (rows 35 67 13 280 84 32 64 128 256), losses := [] }

theorem u3053 : Upper (D 3) (R 3) [34,65,9,272,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3053
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b3054 : PairBound 9 := { available := 133, camps := [{ cop := 4, region := 3, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 13 280 112 165 197 133 389), lower := (rows 35 67 13 280 112 32 64 128 256), losses := [] }

theorem u3054 : Upper (D 3) (R 3) [34,65,9,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3054
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3055 : Route 9 := (fun mask => (mask,id))

def c3055 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3055 : Upper (D 3) (R 3) [34,65,9,272,129] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,129] 13 (by decide) (choices 1) [4,64,128] r3055 c3055
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u980
  · exact u981
  · exact u982

def r3056 : Route 9 := (fun mask => (mask,id))

def c3056 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u3056 : Upper (D 3) (R 3) [34,65,9,272,132] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,132] 13 (by decide) (choices 1) [1,64,128] r3056 c3056
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u983
  · exact u984
  · exact u985

def b3057 : PairBound 9 := { available := 197, camps := [{ cop := 2, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 280 176 229 197 197 453), lower := (rows 35 67 13 280 176 32 64 128 256), losses := [] }

theorem u3057 : Upper (D 3) (R 3) [34,65,9,272,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3057
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r3058 : Route 9 := (fun mask => (mask,id))

def c3058 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3058 : Upper (D 3) (R 3) [34,65,9,272,192] 13 := by
  apply FastRouting.sound _ _ [34,65,9,272,192] 13 (by decide) (choices 1) [1,4,128] r3058 c3058
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u986
  · exact u987
  · exact u988

def b3059 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 296 84 177 209 145 401), lower := (rows 35 67 13 296 84 32 64 128 256), losses := [] }

theorem u3059 : Upper (D 3) (R 3) [34,65,9,288,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b3059
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u3059
end Delivery.IrregularNine14.P03
