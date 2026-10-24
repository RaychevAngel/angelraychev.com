import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0018
import IrregularNine14P10C0019

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r2460 : Route 9 := (fun mask => (mask,id))

def c2460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2460 : Upper (D 10) (R 10) [66,132,288,160,320] 13 := by
  apply FastRouting.sound _ _ [66,132,288,160,320] 13 (by decide) (choices 1) [1,8,16] r2460 c2460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1080
  · exact u1081
  · exact u1082

def r2461 : Route 9 := (fun mask => (mask,id))

def c2461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2461 : Upper (D 10) (R 10) [66,132,288,192,264] 13 := by
  apply FastRouting.sound _ _ [66,132,288,192,264] 13 (by decide) (choices 1) [1,16] r2461 c2461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1083
  · exact u1084

def b2462 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 134 292 200 304 57 121 185 313), lower := (rows 67 134 292 200 304 32 64 128 256), losses := [] }

theorem u2462 : Upper (D 10) (R 10) [66,132,288,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2462 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2463 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 152 304 41 105 169 297), lower := (rows 67 134 324 152 304 32 64 128 256), losses := [] }

theorem u2463 : Upper (D 10) (R 10) [66,132,320,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2463 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2464 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 168 280 49 113 177 305), lower := (rows 67 134 324 168 280 32 64 128 256), losses := [] }

theorem u2464 : Upper (D 10) (R 10) [66,132,320,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2464 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2465 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 134 324 168 304 57 121 185 313), lower := (rows 67 134 324 168 304 32 64 128 256), losses := [] }

theorem u2465 : Upper (D 10) (R 10) [66,132,320,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2465 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2466 : PairBound 9 := { available := 41, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 88 304 41 105 169 297), lower := (rows 67 134 388 88 304 32 64 128 256), losses := [] }

theorem u2466 : Upper (D 10) (R 10) [66,132,384,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2466 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2467 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 104 280 49 113 177 305), lower := (rows 67 134 388 104 280 32 64 128 256), losses := [] }

theorem u2467 : Upper (D 10) (R 10) [66,132,384,96,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2467 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2468 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7),(3,7)], upper := (rows 67 134 388 104 304 57 121 185 313), lower := (rows 67 134 388 104 304 32 64 128 256), losses := [] }

theorem u2468 : Upper (D 10) (R 10) [66,132,384,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2468 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2469 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 67 162 76 168 304 309 341 405 277), lower := (rows 67 162 76 168 304 32 64 128 256), losses := [] }

theorem u2469 : Upper (D 10) (R 10) [66,160,72,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2469 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2470 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 67 162 76 296 176 309 341 405 277), lower := (rows 67 162 76 296 176 32 64 128 256), losses := [] }

theorem u2470 : Upper (D 10) (R 10) [66,160,72,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2470 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2471_4 : Upper (D 10) (R 10) [66,160,72,288,384,4] 13 :=
  permutation_upper _ _ _ [66,160,72,288,384,1] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1085

def r2471 : Route 9 := (fun mask => (mask,id))

def c2471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2471 : Upper (D 10) (R 10) [66,160,72,288,384] 13 := by
  apply FastRouting.sound _ _ [66,160,72,288,384] 13 (by decide) (choices 1) [1,4,16] r2471 c2471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1085
  · exact m2471_4
  · exact u1086

def r2472 : Route 9 := (fun mask => (mask,id))

def c2472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2472 : Upper (D 10) (R 10) [66,160,72,384,288] 13 := by
  apply FastRouting.sound _ _ [66,160,72,384,288] 13 (by decide) (choices 1) [1,4,16] r2472 c2472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1087
  · exact u1088
  · exact u1089

theorem m2473_8 : Upper (D 10) (R 10) [66,160,96,132,288,8] 13 :=
  permutation_upper _ _ _ [66,160,96,132,288,1] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1090

def r2473 : Route 9 := (fun mask => (mask,id))

def c2473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2473 : Upper (D 10) (R 10) [66,160,96,132,288] 13 := by
  apply FastRouting.sound _ _ [66,160,96,132,288] 13 (by decide) (choices 1) [1,8,16,256] r2473 c2473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1090
  · exact m2473_8
  · exact u1091
  · exact u1092

def r2474 : Route 9 := (fun mask => (mask,id))

def c2474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u2474 : Upper (D 10) (R 10) [66,160,96,144,288] 13 := by
  apply FastRouting.sound _ _ [66,160,96,144,288] 13 (by decide) (choices 1) [1,4,8,256] r2474 c2474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1093
  · exact u1094
  · exact u1095
  · exact u1096

def b2475 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 67 162 100 168 276 313 345 409 281), lower := (rows 67 162 100 168 276 32 64 128 256), losses := [] }

theorem u2475 : Upper (D 10) (R 10) [66,160,96,160,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2475 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2476 : PairBound 9 := { available := 277, camps := [{ cop := 1, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 67 162 100 168 280 309 341 405 277), lower := (rows 67 162 100 168 280 32 64 128 256), losses := [] }

theorem u2476 : Upper (D 10) (R 10) [66,160,96,160,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2476 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2477 : Route 9 := (fun mask => (mask,id))

def c2477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2477 : Upper (D 10) (R 10) [66,160,96,260,384] 13 := by
  apply FastRouting.sound _ _ [66,160,96,260,384] 13 (by decide) (choices 1) [1,8,16] r2477 c2477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1097
  · exact u1098
  · exact u1099

def b2478 : PairBound 9 := { available := 45, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 162 100 280 400 45 109 173 301), lower := (rows 67 162 100 280 400 32 64 128 256), losses := [] }

theorem u2478 : Upper (D 10) (R 10) [66,160,96,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2478 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2479 : Route 9 := (fun mask => (mask,id))

def c2479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2479 : Upper (D 10) (R 10) [66,160,96,288,384] 13 := by
  apply FastRouting.sound _ _ [66,160,96,288,384] 13 (by decide) (choices 1) [1,4,8,16] r2479 c2479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1100
  · exact u1101
  · exact u1102
  · exact u1103

def r2480 : Route 9 := (fun mask => (mask,id))

def c2480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2480 : Upper (D 10) (R 10) [66,160,136,320,288] 13 := by
  apply FastRouting.sound _ _ [66,160,136,320,288] 13 (by decide) (choices 1) [1,4,16] r2480 c2480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1104
  · exact u1105
  · exact u1106

def b2481 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 268 336 57 121 185 313), lower := (rows 67 162 164 268 336 32 64 128 256), losses := [] }

theorem u2481 : Upper (D 10) (R 10) [66,160,160,260,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2481 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b2482 : PairBound 9 := { available := 29, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 296 336 61 93 157 285), lower := (rows 67 162 164 296 336 32 64 128 256), losses := [] }

theorem u2482 : Upper (D 10) (R 10) [66,160,160,288,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2482 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r2483 : Route 9 := (fun mask => (mask,id))

def c2483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2483 : Upper (D 10) (R 10) [66,160,192,260,288] 13 := by
  apply FastRouting.sound _ _ [66,160,192,260,288] 13 (by decide) (choices 1) [1,8,16] r2483 c2483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1107
  · exact u1108
  · exact u1109

def b2484 : PairBound 9 := { available := 29, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 67 162 196 296 304 61 93 157 285), lower := (rows 67 162 196 296 304 32 64 128 256), losses := [] }

theorem u2484 : Upper (D 10) (R 10) [66,160,192,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2484 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2485_16 : Upper (D 10) (R 10) [66,384,96,160,288,16] 13 :=
  permutation_upper _ _ _ [66,384,96,160,288,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1112

def r2485 : Route 9 := (fun mask => (mask,id))

def c2485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u2485 : Upper (D 10) (R 10) [66,384,96,160,288] 13 := by
  apply FastRouting.sound _ _ [66,384,96,160,288] 13 (by decide) (choices 1) [1,4,8,16] r2485 c2485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1110
  · exact u1111
  · exact u1112
  · exact m2485_16

def r2486 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2486 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2486 : Upper (D 10) (R 10) [6,9,48,96] 13 := by
  apply FastRouting.sound _ _ [6,9,48,96] 13 (by decide) (choices 2) [96,160,192,384] r2486 c2486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1113
  · exact u1114
  · exact u1115
  · exact u1116

def r2487 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2487 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2487 : Upper (D 10) (R 10) [6,9,48,192] 13 := by
  apply FastRouting.sound _ _ [6,9,48,192] 13 (by decide) (choices 2) [96,192,288,320] r2487 c2487
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1117
  · exact u1118
  · exact u1119
  · exact u1120

def r2488 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2488 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2488 : Upper (D 10) (R 10) [6,9,80,96] 13 := by
  apply FastRouting.sound _ _ [6,9,80,96] 13 (by decide) (choices 2) [160,384] r2488 c2488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1121
  · exact u1122

def r2489 : Route 9 := (fun mask => (mask,id))

def c2489 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2489 : Upper (D 10) (R 10) [6,9,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2489 c2489
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1123
  · exact u1124
  · exact u1125
  · exact u1126
  · exact u1127
  · exact u1128

def r2490 : Route 9 := (fun mask => (mask,id))

def c2490 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2490 : Upper (D 10) (R 10) [6,9,80,192] 13 := by
  apply FastRouting.sound _ _ [6,9,80,192] 13 (by decide) (choices 2) [160,288,384] r2490 c2490
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131

def r2491 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2491 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2491 : Upper (D 10) (R 10) [6,9,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384] 13 (by decide) (choices 2) [96,160,192,384] r2491 c2491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1132
  · exact u1133
  · exact u1134
  · exact u1135

def b2492 : PairBound 9 := { available := 432, camps := [{ cop := 2, region := 11, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 11 100 104 432 432 496 432 432), lower := (rows 7 11 100 104 16 32 64 128 256), losses := [] }

theorem u2492 : Upper (D 10) (R 10) [6,9,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2492 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2493_160 : Upper (D 10) (R 10) [6,9,96,160,160] 13 :=
  permutation_upper _ _ _ [6,9,96,160,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1138

theorem m2493_384 : Upper (D 10) (R 10) [6,9,96,160,384] 13 :=
  permutation_upper _ _ _ [6,9,96,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1141

def r2493 : Route 9 := (fun mask => (mask,id))

def c2493 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2493 : Upper (D 10) (R 10) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2493 c2493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u1138
  · exact m2493_160
  · exact u1139
  · exact u1140
  · exact u1141
  · exact m2493_384

def r2494 : Route 9 := (fun mask => (mask,id))

def c2494 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2494 : Upper (D 10) (R 10) [6,9,96,192] 13 := by
  apply FastRouting.sound _ _ [6,9,96,192] 13 (by decide) (choices 2) [160,288,384] r2494 c2494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1142
  · exact u1143
  · exact u1144

def r2495 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2495 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2495 : Upper (D 10) (R 10) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [96,160,192,384] r2495 c2495
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1145
  · exact u1146
  · exact u1147
  · exact u1148

def b2496 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 11, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 11 196 200 304 304 368 432 304), lower := (rows 7 11 196 200 16 32 64 128 256), losses := [] }

theorem u2496 : Upper (D 10) (R 10) [6,9,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2496 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2497_288 : Upper (D 10) (R 10) [6,9,192,320,288] 13 :=
  permutation_upper _ _ _ [6,9,192,320,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1150

def r2497 : Route 9 := (fun mask => (mask,id))

def c2497 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2497 : Upper (D 10) (R 10) [6,9,192,320] 13 := by
  apply FastRouting.sound _ _ [6,9,192,320] 13 (by decide) (choices 2) [160,288,384] r2497 c2497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1150
  · exact m2497_288
  · exact u1151

def b2498 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 4, targets := 192 }], pairs := [(2,6),(2,7)], upper := (rows 7 19 44 104 496 480 480 480 480), lower := (rows 7 19 44 104 16 32 64 128 256), losses := [] }

theorem u2498 : Upper (D 10) (R 10) [6,17,40,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2498 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2499_96 : Upper (D 10) (R 10) [6,17,40,192,96] 13 :=
  permutation_upper _ _ _ [6,9,48,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1115

theorem m2499_192 : Upper (D 10) (R 10) [6,17,40,192,192] 13 :=
  permutation_upper _ _ _ [6,9,48,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1118

theorem m2499_288 : Upper (D 10) (R 10) [6,17,40,192,288] 13 :=
  permutation_upper _ _ _ [6,9,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1116

theorem m2499_320 : Upper (D 10) (R 10) [6,17,40,192,320] 13 :=
  permutation_upper _ _ _ [6,9,48,192,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1120

def r2499 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2499 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2499 : Upper (D 10) (R 10) [6,17,40,192] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192] 13 (by decide) (choices 2) [96,192,288,320] r2499 c2499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2499_96
  · exact m2499_192
  · exact m2499_288
  · exact m2499_320

def b2500 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 19 76 104 432 416 480 416 416), lower := (rows 7 19 76 104 16 32 64 128 256), losses := [] }

theorem u2500 : Upper (D 10) (R 10) [6,17,72,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2500 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2501_96 : Upper (D 10) (R 10) [6,17,72,160,96] 13 :=
  permutation_upper _ _ _ [6,9,80,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1121

theorem m2501_160 : Upper (D 10) (R 10) [6,17,72,160,160] 13 :=
  permutation_upper _ _ _ [6,9,80,160,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1124

theorem m2501_192 : Upper (D 10) (R 10) [6,17,72,160,192] 13 :=
  permutation_upper _ _ _ [6,9,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1129

theorem m2501_288 : Upper (D 10) (R 10) [6,17,72,160,288] 13 :=
  permutation_upper _ _ _ [6,9,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1126

theorem m2501_320 : Upper (D 10) (R 10) [6,17,72,160,320] 13 :=
  permutation_upper _ _ _ [6,9,80,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1130

theorem m2501_384 : Upper (D 10) (R 10) [6,17,72,160,384] 13 :=
  permutation_upper _ _ _ [6,9,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1133

def r2501 : Route 9 := (fun mask => (mask,id))

def c2501 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2501 : Upper (D 10) (R 10) [6,17,72,160] 13 := by
  apply FastRouting.sound _ _ [6,17,72,160] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2501 c2501
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2501_96
  · exact m2501_160
  · exact m2501_192
  · exact m2501_288
  · exact m2501_320
  · exact m2501_384

def b2502 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 19 76 200 432 416 480 416 416), lower := (rows 7 19 76 200 16 32 64 128 256), losses := [] }

theorem u2502 : Upper (D 10) (R 10) [6,17,72,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2502 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2503_96 : Upper (D 10) (R 10) [6,17,72,384,96] 13 :=
  permutation_upper _ _ _ [6,9,80,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1122

theorem m2503_160 : Upper (D 10) (R 10) [6,17,72,384,160] 13 :=
  permutation_upper _ _ _ [6,9,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1128

theorem m2503_192 : Upper (D 10) (R 10) [6,17,72,384,192] 13 :=
  permutation_upper _ _ _ [6,9,80,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1131

theorem m2503_384 : Upper (D 10) (R 10) [6,17,72,384,384] 13 :=
  permutation_upper _ _ _ [6,9,80,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1135

def r2503 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2503 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2503 : Upper (D 10) (R 10) [6,17,72,384] 13 := by
  apply FastRouting.sound _ _ [6,17,72,384] 13 (by decide) (choices 2) [96,160,192,384] r2503 c2503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2503_96
  · exact m2503_160
  · exact m2503_192
  · exact m2503_384

def b2504 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 19 100 104 440 424 488 424 424), lower := (rows 7 19 100 104 16 32 64 128 256), losses := [] }

theorem u2504 : Upper (D 10) (R 10) [6,17,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2504 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2505_40 : Upper (D 10) (R 10) [6,17,96,160,40] 13 :=
  permutation_upper _ _ _ [6,9,48,96,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1114

theorem m2505_72 : Upper (D 10) (R 10) [6,17,96,160,72] 13 :=
  permutation_upper _ _ _ [6,9,80,96,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1121

theorem m2505_96 : Upper (D 10) (R 10) [6,17,96,160,96] 13 :=
  permutation_upper _ _ _ [6,9,96,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1136

theorem m2505_136 : Upper (D 10) (R 10) [6,17,96,160,136] 13 :=
  permutation_upper _ _ _ [6,9,80,160,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1123

theorem m2505_160 : Upper (D 10) (R 10) [6,17,96,160,160] 13 :=
  permutation_upper _ _ _ [6,9,96,160,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1138

theorem m2505_192 : Upper (D 10) (R 10) [6,17,96,160,192] 13 :=
  permutation_upper _ _ _ [6,9,96,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1142

theorem m2505_264 : Upper (D 10) (R 10) [6,17,96,160,264] 13 :=
  permutation_upper _ _ _ [6,9,80,160,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1126

theorem m2505_288 : Upper (D 10) (R 10) [6,17,96,160,288] 13 :=
  permutation_upper _ _ _ [6,9,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1140

theorem m2505_320 : Upper (D 10) (R 10) [6,17,96,160,320] 13 :=
  permutation_upper _ _ _ [6,9,96,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1143

theorem m2505_384 : Upper (D 10) (R 10) [6,17,96,160,384] 13 :=
  permutation_upper _ _ _ [6,9,96,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1146

def r2505 : Route 9 := (fun mask => (mask,id))

def c2505 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2505 : Upper (D 10) (R 10) [6,17,96,160] 13 := by
  apply FastRouting.sound _ _ [6,17,96,160] 13 (by decide) (choices 2) [40,72,96,136,160,192,264,288,320,384] r2505 c2505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2505_40
  · exact m2505_72
  · exact m2505_96
  · exact m2505_136
  · exact m2505_160
  · exact m2505_192
  · exact m2505_264
  · exact m2505_288
  · exact m2505_320
  · exact m2505_384

theorem m2506_40 : Upper (D 10) (R 10) [6,17,96,192,40] 13 :=
  permutation_upper _ _ _ [6,9,48,96,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1115

theorem m2506_136 : Upper (D 10) (R 10) [6,17,96,192,136] 13 :=
  permutation_upper _ _ _ [6,9,80,160,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1125

theorem m2506_160 : Upper (D 10) (R 10) [6,17,96,192,160] 13 :=
  permutation_upper _ _ _ [6,9,96,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1139

theorem m2506_264 : Upper (D 10) (R 10) [6,17,96,192,264] 13 :=
  permutation_upper _ _ _ [6,9,80,160,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1128

theorem m2506_288 : Upper (D 10) (R 10) [6,17,96,192,288] 13 :=
  permutation_upper _ _ _ [6,9,96,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1141

theorem m2506_384 : Upper (D 10) (R 10) [6,17,96,192,384] 13 :=
  permutation_upper _ _ _ [6,9,96,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1147

def r2506 : Route 9 := (fun mask => (mask,id))

def c2506 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2506 : Upper (D 10) (R 10) [6,17,96,192] 13 := by
  apply FastRouting.sound _ _ [6,17,96,192] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2506 c2506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2506_40
  · exact m2506_136
  · exact m2506_160
  · exact m2506_264
  · exact m2506_288
  · exact m2506_384

theorem m2507_40 : Upper (D 10) (R 10) [6,17,96,384,40] 13 :=
  permutation_upper _ _ _ [6,9,48,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1116

theorem m2507_72 : Upper (D 10) (R 10) [6,17,96,384,72] 13 :=
  permutation_upper _ _ _ [6,9,80,96,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1122

theorem m2507_96 : Upper (D 10) (R 10) [6,17,96,384,96] 13 :=
  permutation_upper _ _ _ [6,9,96,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1137

theorem m2507_136 : Upper (D 10) (R 10) [6,17,96,384,136] 13 :=
  permutation_upper _ _ _ [6,9,80,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1127

theorem m2507_160 : Upper (D 10) (R 10) [6,17,96,384,160] 13 :=
  permutation_upper _ _ _ [6,9,96,160,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1141

theorem m2507_192 : Upper (D 10) (R 10) [6,17,96,384,192] 13 :=
  permutation_upper _ _ _ [6,9,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1144

theorem m2507_384 : Upper (D 10) (R 10) [6,17,96,384,384] 13 :=
  permutation_upper _ _ _ [6,9,96,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1148

def r2507 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2507 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2507 : Upper (D 10) (R 10) [6,17,96,384] 13 := by
  apply FastRouting.sound _ _ [6,17,96,384] 13 (by decide) (choices 2) [40,72,96,136,160,192,384] r2507 c2507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2507_40
  · exact m2507_72
  · exact m2507_96
  · exact m2507_136
  · exact m2507_160
  · exact m2507_192
  · exact m2507_384

theorem m2508_40 : Upper (D 10) (R 10) [6,17,192,96,40] 13 :=
  permutation_upper _ _ _ [6,9,48,192,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1117

theorem m2508_136 : Upper (D 10) (R 10) [6,17,192,96,136] 13 :=
  permutation_upper _ _ _ [6,9,80,192,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1129

theorem m2508_160 : Upper (D 10) (R 10) [6,17,192,96,160] 13 :=
  permutation_upper _ _ _ [6,9,96,192,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1142

theorem m2508_264 : Upper (D 10) (R 10) [6,17,192,96,264] 13 :=
  permutation_upper _ _ _ [6,9,80,384,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1133

theorem m2508_288 : Upper (D 10) (R 10) [6,17,192,96,288] 13 :=
  permutation_upper _ _ _ [6,9,96,384,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1146

theorem m2508_384 : Upper (D 10) (R 10) [6,17,192,96,384] 13 :=
  permutation_upper _ _ _ [6,9,192,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1150

def r2508 : Route 9 := (fun mask => (mask,id))

def c2508 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2508 : Upper (D 10) (R 10) [6,17,192,96] 13 := by
  apply FastRouting.sound _ _ [6,17,192,96] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2508 c2508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2508_40
  · exact m2508_136
  · exact m2508_160
  · exact m2508_264
  · exact m2508_288
  · exact m2508_384

def b2509 : PairBound 9 := { available := 296, camps := [{ cop := 2, region := 8, targets := 288 }], pairs := [(3,5),(3,8)], upper := (rows 7 19 196 200 312 296 360 424 296), lower := (rows 7 19 196 200 16 32 64 128 256), losses := [] }

theorem u2509 : Upper (D 10) (R 10) [6,17,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2509 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2510_40 : Upper (D 10) (R 10) [6,17,192,288,40] 13 :=
  permutation_upper _ _ _ [6,9,48,192,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1119

theorem m2510_72 : Upper (D 10) (R 10) [6,17,192,288,72] 13 :=
  permutation_upper _ _ _ [6,9,80,192,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1130

theorem m2510_96 : Upper (D 10) (R 10) [6,17,192,288,96] 13 :=
  permutation_upper _ _ _ [6,9,96,192,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1143

theorem m2510_192 : Upper (D 10) (R 10) [6,17,192,288,192] 13 :=
  permutation_upper _ _ _ [6,9,192,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1149

theorem m2510_264 : Upper (D 10) (R 10) [6,17,192,288,264] 13 :=
  permutation_upper _ _ _ [6,9,80,384,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1132

theorem m2510_288 : Upper (D 10) (R 10) [6,17,192,288,288] 13 :=
  permutation_upper _ _ _ [6,9,96,384,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1145

theorem m2510_320 : Upper (D 10) (R 10) [6,17,192,288,320] 13 :=
  permutation_upper _ _ _ [6,9,192,320,160] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1150

def r2510 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2510 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u2510 : Upper (D 10) (R 10) [6,17,192,288] 13 := by
  apply FastRouting.sound _ _ [6,17,192,288] 13 (by decide) (choices 2) [40,72,96,192,264,288,320] r2510 c2510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2510_40
  · exact m2510_72
  · exact m2510_96
  · exact m2510_192
  · exact m2510_264
  · exact m2510_288
  · exact m2510_320

theorem m2511_40 : Upper (D 10) (R 10) [6,17,192,320,40] 13 :=
  permutation_upper _ _ _ [6,9,48,192,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1120

theorem m2511_136 : Upper (D 10) (R 10) [6,17,192,320,136] 13 :=
  permutation_upper _ _ _ [6,9,80,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1131

theorem m2511_160 : Upper (D 10) (R 10) [6,17,192,320,160] 13 :=
  permutation_upper _ _ _ [6,9,96,192,384] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1144

theorem m2511_264 : Upper (D 10) (R 10) [6,17,192,320,264] 13 :=
  permutation_upper _ _ _ [6,9,80,384,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1134

theorem m2511_288 : Upper (D 10) (R 10) [6,17,192,320,288] 13 :=
  permutation_upper _ _ _ [6,9,96,384,192] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1147

theorem m2511_384 : Upper (D 10) (R 10) [6,17,192,320,384] 13 :=
  permutation_upper _ _ _ [6,9,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1151

def r2511 : Route 9 := (fun mask => (mask,id))

def c2511 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u2511 : Upper (D 10) (R 10) [6,17,192,320] 13 := by
  apply FastRouting.sound _ _ [6,17,192,320] 13 (by decide) (choices 2) [40,136,160,264,288,384] r2511 c2511
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2511_40
  · exact m2511_136
  · exact m2511_160
  · exact m2511_264
  · exact m2511_288
  · exact m2511_384

def r2512 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2512 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2512 : Upper (D 10) (R 10) [6,24,33,96] 13 := by
  apply FastRouting.sound _ _ [6,24,33,96] 13 (by decide) (choices 2) [96,160,192,384] r2512 c2512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1152
  · exact u1153
  · exact u1154
  · exact u1155

theorem m2513_96 : Upper (D 10) (R 10) [6,24,33,192,96] 13 :=
  permutation_upper _ _ _ [6,24,33,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1154

theorem m2513_288 : Upper (D 10) (R 10) [6,24,33,192,288] 13 :=
  permutation_upper _ _ _ [6,24,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1155

def r2513 : Route 9 := (fun mask => match mask with | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c2513 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2513 : Upper (D 10) (R 10) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [96,192,288,320] r2513 c2513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2513_96
  · exact u1156
  · exact m2513_288
  · exact u1157

def b2514 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 402, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 69 104 432 416 480 416 416), lower := (rows 7 26 69 104 16 32 64 128 256), losses := [] }

theorem u2514 : Upper (D 10) (R 10) [6,24,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2514 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2515_96 : Upper (D 10) (R 10) [6,24,65,160,96] 13 :=
  permutation_upper _ _ _ [6,24,65,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1158

def r2515 : Route 9 := (fun mask => (mask,id))

def c2515 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2515 : Upper (D 10) (R 10) [6,24,65,160] 13 := by
  apply FastRouting.sound _ _ [6,24,65,160] 13 (by decide) (choices 2) [96,160,192,288,320,384] r2515 c2515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m2515_96
  · exact u1160
  · exact u1161
  · exact u1162
  · exact u1163
  · exact u1164

def b2516 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 306, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 69 200 432 416 480 416 416), lower := (rows 7 26 69 200 16 32 64 128 256), losses := [] }

theorem u2516 : Upper (D 10) (R 10) [6,24,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2516 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m2517_96 : Upper (D 10) (R 10) [6,24,65,384,96] 13 :=
  permutation_upper _ _ _ [6,24,65,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1159

theorem m2517_160 : Upper (D 10) (R 10) [6,24,65,384,160] 13 :=
  permutation_upper _ _ _ [6,24,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1164

theorem m2517_192 : Upper (D 10) (R 10) [6,24,65,384,192] 13 :=
  permutation_upper _ _ _ [6,24,65,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1165

def r2517 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2517 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2517 : Upper (D 10) (R 10) [6,24,65,384] 13 := by
  apply FastRouting.sound _ _ [6,24,65,384] 13 (by decide) (choices 2) [96,160,192,384] r2517 c2517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m2517_96
  · exact m2517_160
  · exact m2517_192
  · exact u1166

def r2518 : Route 9 := (fun mask => match mask with | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c2518 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u2518 : Upper (D 10) (R 10) [6,24,96,33] 13 := by
  apply FastRouting.sound _ _ [6,24,96,33] 13 (by decide) (choices 2) [96,160,192,384] r2518 c2518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1167
  · exact u1168
  · exact u1169
  · exact u1170

def b2519 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 26 100 73 432 416 480 416 416), lower := (rows 7 26 100 73 16 32 64 128 256), losses := [] }

theorem u2519 : Upper (D 10) (R 10) [6,24,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b2519 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u2519
end Delivery.IrregularNine14.P10
