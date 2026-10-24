import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0018
import IrregularNine14P08C0019

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7440 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 49 480 480 480 480), lower := (rows 7 42 69 152 49 32 64 128 256), losses := [] }

theorem u7440 : Upper (D 8) (R 8) [6,40,65,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7440 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7441 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 69 152 81 416 480 416 416), lower := (rows 7 42 69 152 81 32 64 128 256), losses := [] }

theorem u7441 : Upper (D 8) (R 8) [6,40,65,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7441 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7442 : Route 9 := (fun mask => (mask,id))

def c7442 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | _ => 0)

theorem u7442 : Upper (D 8) (R 8) [6,40,65,144,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,96] 13 (by decide) (choices 1) [1,128,256] r7442 c7442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1126
  · exact u1127
  · exact u1128

def b7443 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 145 352 352 480 352), lower := (rows 7 42 69 152 145 32 64 128 256), losses := [] }

theorem u7443 : Upper (D 8) (R 8) [6,40,65,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7443 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7444 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 176 353 353 481 353), lower := (rows 7 42 69 152 176 32 64 128 256), losses := [] }

theorem u7444 : Upper (D 8) (R 8) [6,40,65,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7444 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7445 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 208 289 353 417 289), lower := (rows 7 42 69 152 208 32 64 128 256), losses := [] }

theorem u7445 : Upper (D 8) (R 8) [6,40,65,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7445 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7446 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 234, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 152 273 224 224 224 480), lower := (rows 7 42 69 152 273 32 64 128 256), losses := [] }

theorem u7446 : Upper (D 8) (R 8) [6,40,65,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7446 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7447 : Route 9 := (fun mask => (mask,id))

def c7447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7447 : Upper (D 8) (R 8) [6,40,65,144,288] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,288] 13 (by decide) (choices 1) [1,64,128] r7447 c7447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1129
  · exact u1130
  · exact u1131

def r7448 : Route 9 := (fun mask => (mask,id))

def c7448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7448 : Upper (D 8) (R 8) [6,40,65,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,65,144,320] 13 (by decide) (choices 1) [1,128] r7448 c7448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1132
  · exact u1133

def b7449 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 69 152 400 97 97 225 353), lower := (rows 7 42 69 152 400 32 64 128 256), losses := [] }

theorem u7449 : Upper (D 8) (R 8) [6,40,65,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7449 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7450 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 49 224 224 224 480), lower := (rows 7 42 69 280 49 32 64 128 256), losses := [] }

theorem u7450 : Upper (D 8) (R 8) [6,40,65,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7451 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 69 280 81 160 224 160 416), lower := (rows 7 42 69 280 81 32 64 128 256), losses := [] }

theorem u7451 : Upper (D 8) (R 8) [6,40,65,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7451 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7452 : Route 9 := (fun mask => (mask,id))

def c7452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7452 : Upper (D 8) (R 8) [6,40,65,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,96] 13 (by decide) (choices 1) [1,128] r7452 c7452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1134
  · exact u1135

def b7453 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 280 145 224 224 224 480), lower := (rows 7 42 69 280 145 32 64 128 256), losses := [] }

theorem u7453 : Upper (D 8) (R 8) [6,40,65,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7454 : Route 9 := (fun mask => (mask,id))

def c7454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7454 : Upper (D 8) (R 8) [6,40,65,272,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,160] 13 (by decide) (choices 1) [1,64,128] r7454 c7454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1136
  · exact u1137
  · exact u1138

def r7455 : Route 9 := (fun mask => (mask,id))

def c7455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7455 : Upper (D 8) (R 8) [6,40,65,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,272,192] 13 (by decide) (choices 1) [1,128] r7455 c7455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1139
  · exact u1140

def b7456 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 458, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 49 240 240 240 496), lower := (rows 7 42 69 392 49 32 64 128 256), losses := [] }

theorem u7456 : Upper (D 8) (R 8) [6,40,65,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7457 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 69 392 81 176 240 176 432), lower := (rows 7 42 69 392 81 32 64 128 256), losses := [] }

theorem u7457 : Upper (D 8) (R 8) [6,40,65,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7458 : Route 9 := (fun mask => (mask,id))

def c7458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7458 : Upper (D 8) (R 8) [6,40,65,384,96] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,96] 13 (by decide) (choices 1) [1,16,128] r7458 c7458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1141
  · exact u1142
  · exact u1143

def b7459 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 362, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 69 392 145 112 112 240 368), lower := (rows 7 42 69 392 145 32 64 128 256), losses := [] }

theorem u7459 : Upper (D 8) (R 8) [6,40,65,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7460 : Route 9 := (fun mask => (mask,id))

def c7460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7460 : Upper (D 8) (R 8) [6,40,65,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,160] 13 (by decide) (choices 1) [1,16,64] r7460 c7460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1144
  · exact u1145
  · exact u1146

def r7461 : Route 9 := (fun mask => (mask,id))

def c7461 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7461 : Upper (D 8) (R 8) [6,40,65,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,65,384,192] 13 (by decide) (choices 1) [1,16] r7461 c7461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1147
  · exact u1148

def b7462 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 354, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 137 49 480 480 480 480), lower := (rows 7 42 84 137 49 32 64 128 256), losses := [] }

theorem u7462 : Upper (D 8) (R 8) [6,40,80,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7463 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 81 416 480 416 416), lower := (rows 7 42 84 137 81 32 64 128 256), losses := [] }

theorem u7463 : Upper (D 8) (R 8) [6,40,80,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7464 : PairBound 9 := { available := 417, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 112 417 481 417 417), lower := (rows 7 42 84 137 112 32 64 128 256), losses := [] }

theorem u7464 : Upper (D 8) (R 8) [6,40,80,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7465 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 84 137 145 352 352 480 352), lower := (rows 7 42 84 137 145 32 64 128 256), losses := [] }

theorem u7465 : Upper (D 8) (R 8) [6,40,80,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7466 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 84 137 176 353 353 481 353), lower := (rows 7 42 84 137 176 32 64 128 256), losses := [] }

theorem u7466 : Upper (D 8) (R 8) [6,40,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7467 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 208 289 353 417 289), lower := (rows 7 42 84 137 208 32 64 128 256), losses := [] }

theorem u7467 : Upper (D 8) (R 8) [6,40,80,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7468 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 137 273 224 224 224 480), lower := (rows 7 42 84 137 273 32 64 128 256), losses := [] }

theorem u7468 : Upper (D 8) (R 8) [6,40,80,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7469 : Route 9 := (fun mask => (mask,id))

def c7469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7469 : Upper (D 8) (R 8) [6,40,80,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,288] 13 (by decide) (choices 1) [1,64,128] r7469 c7469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1149
  · exact u1150
  · exact u1151

def b7470 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 171, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 137 336 161 225 161 417), lower := (rows 7 42 84 137 336 32 64 128 256), losses := [] }

theorem u7470 : Upper (D 8) (R 8) [6,40,80,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7471 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 7 42 84 137 400 97 97 225 353), lower := (rows 7 42 84 137 400 32 64 128 256), losses := [] }

theorem u7471 : Upper (D 8) (R 8) [6,40,80,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7472 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 265 49 224 224 224 480), lower := (rows 7 42 84 265 49 32 64 128 256), losses := [] }

theorem u7472 : Upper (D 8) (R 8) [6,40,80,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7473 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 265 81 160 224 160 416), lower := (rows 7 42 84 265 81 32 64 128 256), losses := [] }

theorem u7473 : Upper (D 8) (R 8) [6,40,80,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7474 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 265 112 161 225 161 417), lower := (rows 7 42 84 265 112 32 64 128 256), losses := [] }

theorem u7474 : Upper (D 8) (R 8) [6,40,80,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7475 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 84 265 145 224 224 224 480), lower := (rows 7 42 84 265 145 32 64 128 256), losses := [] }

theorem u7475 : Upper (D 8) (R 8) [6,40,80,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7476 : Route 9 := (fun mask => (mask,id))

def c7476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7476 : Upper (D 8) (R 8) [6,40,80,257,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,257,160] 13 (by decide) (choices 1) [1,64,128] r7476 c7476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1152
  · exact u1153
  · exact u1154

def b7477 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 265 208 161 225 161 417), lower := (rows 7 42 84 265 208 32 64 128 256), losses := [] }

theorem u7477 : Upper (D 8) (R 8) [6,40,80,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7478 : Route 9 := (fun mask => (mask,id))

def c7478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7478 : Upper (D 8) (R 8) [6,40,80,384,33] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,33] 13 (by decide) (choices 1) [1,64,128] r7478 c7478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1155
  · exact u1156
  · exact u1157

def b7479 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 392 81 161 225 161 417), lower := (rows 7 42 84 392 81 32 64 128 256), losses := [] }

theorem u7479 : Upper (D 8) (R 8) [6,40,80,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7480 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 392 112 161 225 161 417), lower := (rows 7 42 84 392 112 32 64 128 256), losses := [] }

theorem u7480 : Upper (D 8) (R 8) [6,40,80,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7480 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7481 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 7 42 84 392 145 97 97 225 353), lower := (rows 7 42 84 392 145 32 64 128 256), losses := [] }

theorem u7481 : Upper (D 8) (R 8) [6,40,80,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7481 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7482 : Route 9 := (fun mask => (mask,id))

def c7482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7482 : Upper (D 8) (R 8) [6,40,80,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160] 13 (by decide) (choices 1) [1,64] r7482 c7482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1158
  · exact u1159

def b7483 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 84 392 208 33 97 161 289), lower := (rows 7 42 84 392 208 32 64 128 256), losses := [] }

theorem u7483 : Upper (D 8) (R 8) [6,40,80,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7483 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7484 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 27, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 100 25 49 480 448 448 448), lower := (rows 7 42 100 25 49 32 64 128 256), losses := [] }

theorem u7484 : Upper (D 8) (R 8) [6,40,96,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7484 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7485 : PairBound 9 := { available := 416, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 81 416 480 416 416), lower := (rows 7 42 100 25 81 32 64 128 256), losses := [] }

theorem u7485 : Upper (D 8) (R 8) [6,40,96,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7485 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7486 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 27, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 25 112 417 449 385 385), lower := (rows 7 42 100 25 112 32 64 128 256), losses := [] }

theorem u7486 : Upper (D 8) (R 8) [6,40,96,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7486 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7487 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 25 145 480 480 480 480), lower := (rows 7 42 100 25 145 32 64 128 256), losses := [] }

theorem u7487 : Upper (D 8) (R 8) [6,40,96,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7487 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7488 : Route 9 := (fun mask => (mask,id))

def c7488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u7488 : Upper (D 8) (R 8) [6,40,96,17,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,160] 13 (by decide) (choices 1) [1,64,128,256] r7488 c7488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1160
  · exact u1161
  · exact u1162
  · exact u1163

def b7489 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 25 208 417 481 417 417), lower := (rows 7 42 100 25 208 32 64 128 256), losses := [] }

theorem u7489 : Upper (D 8) (R 8) [6,40,96,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7489 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7490 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 25 273 224 224 224 480), lower := (rows 7 42 100 25 273 32 64 128 256), losses := [] }

theorem u7490 : Upper (D 8) (R 8) [6,40,96,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7490 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7491 : Route 9 := (fun mask => (mask,id))

def c7491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7491 : Upper (D 8) (R 8) [6,40,96,17,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,288] 13 (by decide) (choices 1) [1,64,128] r7491 c7491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1164
  · exact u1165
  · exact u1166

def b7492 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 25 336 161 225 161 417), lower := (rows 7 42 100 25 336 32 64 128 256), losses := [] }

theorem u7492 : Upper (D 8) (R 8) [6,40,96,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7492 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7493 : Route 9 := (fun mask => (mask,id))

def c7493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7493 : Upper (D 8) (R 8) [6,40,96,17,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,17,384] 13 (by decide) (choices 1) [1,64,128] r7493 c7493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1167
  · exact u1168
  · exact u1169

def b7494 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 452, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 49 496 464 464 464), lower := (rows 7 42 100 137 49 32 64 128 256), losses := [] }

theorem u7494 : Upper (D 8) (R 8) [6,40,96,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7494 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7495 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 137 81 432 496 432 432), lower := (rows 7 42 100 137 81 32 64 128 256), losses := [] }

theorem u7495 : Upper (D 8) (R 8) [6,40,96,129,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7495 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7496 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 100 137 112 433 465 401 401), lower := (rows 7 42 100 137 112 32 64 128 256), losses := [] }

theorem u7496 : Upper (D 8) (R 8) [6,40,96,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7496 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7497 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 100 137 145 368 368 496 368), lower := (rows 7 42 100 137 145 32 64 128 256), losses := [] }

theorem u7497 : Upper (D 8) (R 8) [6,40,96,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7497 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7498 : Route 9 := (fun mask => (mask,id))

def c7498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u7498 : Upper (D 8) (R 8) [6,40,96,129,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,160] 13 (by decide) (choices 1) [1,16,64,256] r7498 c7498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1170
  · exact u1171
  · exact u1172
  · exact u1173

def r7499 : Route 9 := (fun mask => (mask,id))

def c7499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u7499 : Upper (D 8) (R 8) [6,40,96,129,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,192] 13 (by decide) (choices 1) [1,16,256] r7499 c7499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1174
  · exact u1175
  · exact u1176

#print axioms u7499
end Delivery.IrregularNine14.P08
