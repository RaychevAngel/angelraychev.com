import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0217
import IrregularNine14P06C0218

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b31080 : PairBound 9 := { available := 263, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 2, region := 290, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 69 56 208 295 327 391 263), lower := (rows 11 38 69 56 208 32 64 128 256), losses := [] }

theorem u31080 : Upper (D 6) (R 6) [10,36,65,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31080 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31081 : Route 9 := (fun mask => (mask,id))

def c31081 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31081 : Upper (D 6) (R 6) [10,36,65,48,384] 13 := by
  apply FastRouting.sound _ _ [10,36,65,48,384] 13 (by decide) (choices 1) [1,2,4,64] r31081 c31081
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13023
  · exact u13024
  · exact u13025
  · exact u13026

def b31082 : PairBound 9 := { available := 420, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 69 88 19 420 484 420 420), lower := (rows 11 38 69 88 19 32 64 128 256), losses := [] }

theorem u31082 : Upper (D 6) (R 6) [10,36,65,80,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31082 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31083 : PairBound 9 := { available := 418, camps := [{ cop := 2, region := 24, targets := 34 }], pairs := [(3,1),(3,5),(4,1)], upper := (rows 11 38 69 88 21 418 482 418 418), lower := (rows 11 38 69 88 21 32 64 128 256), losses := [] }

theorem u31083 : Upper (D 6) (R 6) [10,36,65,80,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31083 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31084 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 69 88 22 417 481 417 417), lower := (rows 11 38 69 88 22 32 64 128 256), losses := [] }

theorem u31084 : Upper (D 6) (R 6) [10,36,65,80,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31084 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31085 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 452, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 38 69 88 49 422 454 390 390), lower := (rows 11 38 69 88 49 32 64 128 256), losses := [] }

theorem u31085 : Upper (D 6) (R 6) [10,36,65,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31085 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31086 : PairBound 9 := { available := 389, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 69 88 50 421 453 389 389), lower := (rows 11 38 69 88 50 32 64 128 256), losses := [] }

theorem u31086 : Upper (D 6) (R 6) [10,36,65,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31086 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31087 : PairBound 9 := { available := 387, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 69 88 52 419 451 387 387), lower := (rows 11 38 69 88 52 32 64 128 256), losses := [] }

theorem u31087 : Upper (D 6) (R 6) [10,36,65,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31087 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31088 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0),(1,6),(4,6)], upper := (rows 11 38 69 88 145 294 358 422 294), lower := (rows 11 38 69 88 145 32 64 128 256), losses := [] }

theorem u31088 : Upper (D 6) (R 6) [10,36,65,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31088 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31089 : PairBound 9 := { available := 293, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 356, targets := 2 }], pairs := [(1,6),(2,1),(4,6)], upper := (rows 11 38 69 88 146 293 357 421 293), lower := (rows 11 38 69 88 146 32 64 128 256), losses := [] }

theorem u31089 : Upper (D 6) (R 6) [10,36,65,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31089 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31090 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 434, targets := 64 }], pairs := [(0,6),(1,6),(4,6)], upper := (rows 11 38 69 88 148 291 355 419 291), lower := (rows 11 38 69 88 148 32 64 128 256), losses := [{ target := 6, region := (rows 9 22 4 8 22 45 0 141 269), good := (rows 443 438 439 443 438 32 0 128 256) }] }

theorem u31090 : Upper (D 6) (R 6) [10,36,65,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31090 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31091 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 434, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(1,6),(2,5),(4,6)], upper := (rows 11 38 69 88 176 295 327 391 263), lower := (rows 11 38 69 88 176 32 64 128 256), losses := [] }

theorem u31091 : Upper (D 6) (R 6) [10,36,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31091 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31092 : Route 9 := (fun mask => (mask,id))

def c31092 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31092 : Upper (D 6) (R 6) [10,36,65,80,384] 13 := by
  apply FastRouting.sound _ _ [10,36,65,80,384] 13 (by decide) (choices 1) [1,2,4] r31092 c31092
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13027
  · exact u13028
  · exact u13029

def b31093 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 16, targets := 96 },{ cop := 2, region := 306, targets := 1 }], pairs := [(1,0),(4,5),(4,6)], upper := (rows 11 38 69 137 22 368 368 496 368), lower := (rows 11 38 69 137 22 32 64 128 256), losses := [] }

theorem u31093 : Upper (D 6) (R 6) [10,36,65,129,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31093 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31094 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 461, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 11 38 69 137 50 372 340 468 340), lower := (rows 11 38 69 137 50 32 64 128 256), losses := [] }

theorem u31094 : Upper (D 6) (R 6) [10,36,65,129,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31094 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31095 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 306, targets := 1 },{ cop := 1, region := 16, targets := 2 }], pairs := [(1,0),(4,0),(4,1)], upper := (rows 11 38 69 137 52 370 338 466 338), lower := (rows 11 38 69 137 52 32 64 128 256), losses := [] }

theorem u31095 : Upper (D 6) (R 6) [10,36,65,129,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31095 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31096 : Route 9 := (fun mask => (mask,id))

def c31096 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31096 : Upper (D 6) (R 6) [10,36,65,129,66] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,66] 13 (by decide) (choices 1) [4,16,256] r31096 c31096
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13030
  · exact u13031
  · exact u13032

def b31097 : PairBound 9 := { available := 306, camps := [{ cop := 4, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 38 69 137 84 306 370 434 306), lower := (rows 11 38 69 137 84 32 64 128 256), losses := [] }

theorem u31097 : Upper (D 6) (R 6) [10,36,65,129,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31097 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31098 : Route 9 := (fun mask => (mask,id))

def c31098 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31098 : Upper (D 6) (R 6) [10,36,65,129,96] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,96] 13 (by decide) (choices 1) [2,4,16,256] r31098 c31098
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13033
  · exact u13034
  · exact u13035
  · exact u13036

def r31099 : Route 9 := (fun mask => (mask,id))

def c31099 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31099 : Upper (D 6) (R 6) [10,36,65,129,258] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,258] 13 (by decide) (choices 1) [4,16,64] r31099 c31099
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13037
  · exact u13038
  · exact u13039

def r31100 : Route 9 := (fun mask => (mask,id))

def c31100 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31100 : Upper (D 6) (R 6) [10,36,65,129,260] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,260] 13 (by decide) (choices 1) [2,16,64] r31100 c31100
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13040
  · exact u13041
  · exact u13042

def r31101 : Route 9 := (fun mask => (mask,id))

def c31101 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31101 : Upper (D 6) (R 6) [10,36,65,129,288] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,288] 13 (by decide) (choices 1) [2,4,16,64] r31101 c31101
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13043
  · exact u13044
  · exact u13045
  · exact u13046

def r31102 : Route 9 := (fun mask => (mask,id))

def c31102 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31102 : Upper (D 6) (R 6) [10,36,65,129,320] 13 := by
  apply FastRouting.sound _ _ [10,36,65,129,320] 13 (by decide) (choices 1) [2,4,16] r31102 c31102
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13047
  · exact u13048
  · exact u13049

def b31103 : PairBound 9 := { available := 368, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 38 69 140 19 368 368 496 368), lower := (rows 11 38 69 140 19 32 64 128 256), losses := [] }

theorem u31103 : Upper (D 6) (R 6) [10,36,65,132,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31103 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31104 : Route 9 := (fun mask => (mask,id))

def c31104 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31104 : Upper (D 6) (R 6) [10,36,65,132,33] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,33] 13 (by decide) (choices 1) [2,16,64,256] r31104 c31104
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13050
  · exact u13051
  · exact u13052
  · exact u13053

def b31105 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 69 140 50 369 337 465 337), lower := (rows 11 38 69 140 50 32 64 128 256), losses := [] }

theorem u31105 : Upper (D 6) (R 6) [10,36,65,132,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31105 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31106 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 38 69 140 81 306 370 434 306), lower := (rows 11 38 69 140 81 32 64 128 256), losses := [] }

theorem u31106 : Upper (D 6) (R 6) [10,36,65,132,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31106 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31107 : Route 9 := (fun mask => (mask,id))

def c31107 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31107 : Upper (D 6) (R 6) [10,36,65,132,66] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,66] 13 (by decide) (choices 1) [1,16,256] r31107 c31107
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13054
  · exact u13055
  · exact u13056

def r31108 : Route 9 := (fun mask => (mask,id))

def c31108 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31108 : Upper (D 6) (R 6) [10,36,65,132,96] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,96] 13 (by decide) (choices 1) [1,2,16,256] r31108 c31108
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13057
  · exact u13058
  · exact u13059
  · exact u13060

def r31109 : Route 9 := (fun mask => (mask,id))

def c31109 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31109 : Upper (D 6) (R 6) [10,36,65,132,257] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,257] 13 (by decide) (choices 1) [2,16,64] r31109 c31109
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13061
  · exact u13062
  · exact u13063

def r31110 : Route 9 := (fun mask => (mask,id))

def c31110 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31110 : Upper (D 6) (R 6) [10,36,65,132,258] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,258] 13 (by decide) (choices 1) [1,16,64] r31110 c31110
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13064
  · exact u13065
  · exact u13066

def r31111 : Route 9 := (fun mask => (mask,id))

def c31111 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31111 : Upper (D 6) (R 6) [10,36,65,132,288] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,288] 13 (by decide) (choices 1) [1,2,16,64] r31111 c31111
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13067
  · exact u13068
  · exact u13069
  · exact u13070

def r31112 : Route 9 := (fun mask => (mask,id))

def c31112 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31112 : Upper (D 6) (R 6) [10,36,65,132,320] 13 := by
  apply FastRouting.sound _ _ [10,36,65,132,320] 13 (by decide) (choices 1) [1,2,16] r31112 c31112
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13071
  · exact u13072
  · exact u13073

def b31113 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 69 152 19 356 356 484 356), lower := (rows 11 38 69 152 19 32 64 128 256), losses := [] }

theorem u31113 : Upper (D 6) (R 6) [10,36,65,144,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31113 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31114 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 69 152 21 354 354 482 354), lower := (rows 11 38 69 152 21 32 64 128 256), losses := [] }

theorem u31114 : Upper (D 6) (R 6) [10,36,65,144,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31114 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31115 : PairBound 9 := { available := 353, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 69 152 22 353 353 481 353), lower := (rows 11 38 69 152 22 32 64 128 256), losses := [] }

theorem u31115 : Upper (D 6) (R 6) [10,36,65,144,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31115 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31116 : PairBound 9 := { available := 326, camps := [{ cop := 0, region := 324, targets := 32 },{ cop := 2, region := 290, targets := 1 }], pairs := [(1,0),(2,5),(3,5)], upper := (rows 11 38 69 152 49 358 326 454 326), lower := (rows 11 38 69 152 49 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 21 24 16 0 67 131 259), good := (rows 463 454 453 156 477 0 64 128 256) }] }

theorem u31116 : Upper (D 6) (R 6) [10,36,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31116 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31117 : PairBound 9 := { available := 325, camps := [{ cop := 1, region := 16, targets := 69 }], pairs := [(4,0),(4,2),(4,6)], upper := (rows 11 38 69 152 50 357 325 453 325), lower := (rows 11 38 69 152 50 32 64 128 256), losses := [] }

theorem u31117 : Upper (D 6) (R 6) [10,36,65,144,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31117 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31118 : PairBound 9 := { available := 323, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 69 152 52 355 323 451 323), lower := (rows 11 38 69 152 52 32 64 128 256), losses := [] }

theorem u31118 : Upper (D 6) (R 6) [10,36,65,144,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31118 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31119 : PairBound 9 := { available := 294, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 4, region := 4, targets := 2 }], pairs := [(2,1),(4,1),(4,5)], upper := (rows 11 38 69 152 81 294 358 422 294), lower := (rows 11 38 69 152 81 32 64 128 256), losses := [] }

theorem u31119 : Upper (D 6) (R 6) [10,36,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31119 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31120 : Route 9 := (fun mask => (mask,id))

def c31120 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31120 : Upper (D 6) (R 6) [10,36,65,144,66] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,66] 13 (by decide) (choices 1) [1,4,256] r31120 c31120
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13074
  · exact u13075
  · exact u13076

def b31121 : PairBound 9 := { available := 291, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 69 152 84 291 355 419 291), lower := (rows 11 38 69 152 84 32 64 128 256), losses := [] }

theorem u31121 : Upper (D 6) (R 6) [10,36,65,144,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31121 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31122 : Route 9 := (fun mask => (mask,id))

def c31122 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31122 : Upper (D 6) (R 6) [10,36,65,144,96] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,96] 13 (by decide) (choices 1) [1,2,4,256] r31122 c31122
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13077
  · exact u13078
  · exact u13079
  · exact u13080

def r31123 : Route 9 := (fun mask => (mask,id))

def c31123 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31123 : Upper (D 6) (R 6) [10,36,65,144,257] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,257] 13 (by decide) (choices 1) [2,4,64] r31123 c31123
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13081
  · exact u13082
  · exact u13083

def r31124 : Route 9 := (fun mask => (mask,id))

def c31124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31124 : Upper (D 6) (R 6) [10,36,65,144,258] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,258] 13 (by decide) (choices 1) [1,4,64] r31124 c31124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13084
  · exact u13085
  · exact u13086

def r31125 : Route 9 := (fun mask => (mask,id))

def c31125 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31125 : Upper (D 6) (R 6) [10,36,65,144,260] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,260] 13 (by decide) (choices 1) [1,2,64] r31125 c31125
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13087
  · exact u13088
  · exact u13089

def r31126 : Route 9 := (fun mask => (mask,id))

def c31126 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31126 : Upper (D 6) (R 6) [10,36,65,144,288] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,288] 13 (by decide) (choices 1) [1,2,4,64] r31126 c31126
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13090
  · exact u13091
  · exact u13092
  · exact u13093

def r31127 : Route 9 := (fun mask => (mask,id))

def c31127 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31127 : Upper (D 6) (R 6) [10,36,65,144,320] 13 := by
  apply FastRouting.sound _ _ [10,36,65,144,320] 13 (by decide) (choices 1) [1,2,4] r31127 c31127
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13094
  · exact u13095
  · exact u13096

def b31128 : PairBound 9 := { available := 340, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 11 38 69 168 19 372 340 468 340), lower := (rows 11 38 69 168 19 32 64 128 256), losses := [] }

theorem u31128 : Upper (D 6) (R 6) [10,36,65,160,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31128 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31129 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 98 }], pairs := [(4,1),(4,5),(4,6)], upper := (rows 11 38 69 168 21 370 338 466 338), lower := (rows 11 38 69 168 21 32 64 128 256), losses := [] }

theorem u31129 : Upper (D 6) (R 6) [10,36,65,160,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31129 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31130 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 38 69 168 22 369 337 465 337), lower := (rows 11 38 69 168 22 32 64 128 256), losses := [] }

theorem u31130 : Upper (D 6) (R 6) [10,36,65,160,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31130 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31131 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 2, region := 16, targets := 2 }], pairs := [(2,5),(4,1),(4,5)], upper := (rows 11 38 69 168 81 310 342 406 278), lower := (rows 11 38 69 168 81 32 64 128 256), losses := [] }

theorem u31131 : Upper (D 6) (R 6) [10,36,65,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31131 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31132 : Route 9 := (fun mask => (mask,id))

def c31132 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31132 : Upper (D 6) (R 6) [10,36,65,160,66] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160,66] 13 (by decide) (choices 1) [1,4,16,256] r31132 c31132
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13097
  · exact u13098
  · exact u13099
  · exact u13100

def b31133 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 11 38 69 168 84 307 339 403 275), lower := (rows 11 38 69 168 84 32 64 128 256), losses := [] }

theorem u31133 : Upper (D 6) (R 6) [10,36,65,160,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31133 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31134 : Route 9 := (fun mask => (mask,id))

def c31134 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31134 : Upper (D 6) (R 6) [10,36,65,160,257] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160,257] 13 (by decide) (choices 1) [2,4,16,64] r31134 c31134
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13101
  · exact u13102
  · exact u13103
  · exact u13104

def r31135 : Route 9 := (fun mask => (mask,id))

def c31135 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31135 : Upper (D 6) (R 6) [10,36,65,160,258] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160,258] 13 (by decide) (choices 1) [1,4,16,64] r31135 c31135
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13105
  · exact u13106
  · exact u13107
  · exact u13108

def r31136 : Route 9 := (fun mask => (mask,id))

def c31136 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31136 : Upper (D 6) (R 6) [10,36,65,160,260] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160,260] 13 (by decide) (choices 1) [1,2,16,64] r31136 c31136
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13109
  · exact u13110
  · exact u13111
  · exact u13112

def r31137 : Route 9 := (fun mask => (mask,id))

def c31137 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31137 : Upper (D 6) (R 6) [10,36,65,160,320] 13 := by
  apply FastRouting.sound _ _ [10,36,65,160,320] 13 (by decide) (choices 1) [1,2,4,16] r31137 c31137
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13113
  · exact u13114
  · exact u13115
  · exact u13116

def b31138 : PairBound 9 := { available := 308, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 69 200 19 308 372 436 308), lower := (rows 11 38 69 200 19 32 64 128 256), losses := [] }

theorem u31138 : Upper (D 6) (R 6) [10,36,65,192,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31138 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31139 : PairBound 9 := { available := 306, camps := [{ cop := 2, region := 16, targets := 34 },{ cop := 2, region := 306, targets := 64 }], pairs := [(1,6),(4,1),(4,5)], upper := (rows 11 38 69 200 21 306 370 434 306), lower := (rows 11 38 69 200 21 32 64 128 256), losses := [] }

theorem u31139 : Upper (D 6) (R 6) [10,36,65,192,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31139 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31139
end Delivery.IrregularNine14.P06
