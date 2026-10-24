import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0019
import IrregularNine14P08C0020

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 137 273 240 240 240 496), lower := (rows 7 42 100 137 273 32 64 128 256), losses := [] }

theorem u7500 : Upper (D 8) (R 8) [6,40,96,129,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7500 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7501 : Route 9 := (fun mask => (mask,id))

def c7501 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7501 : Upper (D 8) (R 8) [6,40,96,129,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,288] 13 (by decide) (choices 1) [1,16,64,128] r7501 c7501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1177
  · exact u1178
  · exact u1179
  · exact u1180

def r7502 : Route 9 := (fun mask => (mask,id))

def c7502 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7502 : Upper (D 8) (R 8) [6,40,96,129,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,320] 13 (by decide) (choices 1) [1,16,128] r7502 c7502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1181
  · exact u1182
  · exact u1183

def r7503 : Route 9 := (fun mask => (mask,id))

def c7503 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7503 : Upper (D 8) (R 8) [6,40,96,129,384] 13 := by
  apply FastRouting.sound _ _ [6,40,96,129,384] 13 (by decide) (choices 1) [1,16,64] r7503 c7503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1184
  · exact u1185
  · exact u1186

def b7504 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 152 49 481 449 449 449), lower := (rows 7 42 100 152 49 32 64 128 256), losses := [] }

theorem u7504 : Upper (D 8) (R 8) [6,40,96,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7504 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7505 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 152 81 417 481 417 417), lower := (rows 7 42 100 152 81 32 64 128 256), losses := [] }

theorem u7505 : Upper (D 8) (R 8) [6,40,96,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7505 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7506 : PairBound 9 := { available := 385, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 100 152 112 417 449 385 385), lower := (rows 7 42 100 152 112 32 64 128 256), losses := [] }

theorem u7506 : Upper (D 8) (R 8) [6,40,96,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7506 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7507 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 145 353 353 481 353), lower := (rows 7 42 100 152 145 32 64 128 256), losses := [] }

theorem u7507 : Upper (D 8) (R 8) [6,40,96,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7507 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7508 : PairBound 9 := { available := 321, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 100 152 176 353 321 449 321), lower := (rows 7 42 100 152 176 32 64 128 256), losses := [] }

theorem u7508 : Upper (D 8) (R 8) [6,40,96,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7508 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 208 289 353 417 289), lower := (rows 7 42 100 152 208 32 64 128 256), losses := [] }

theorem u7509 : Upper (D 8) (R 8) [6,40,96,144,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7509 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7510 : Route 9 := (fun mask => (mask,id))

def c7510 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7510 : Upper (D 8) (R 8) [6,40,96,144,257] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,257] 13 (by decide) (choices 1) [1,64,128] r7510 c7510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1187
  · exact u1188
  · exact u1189

def r7511 : Route 9 := (fun mask => (mask,id))

def c7511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7511 : Upper (D 8) (R 8) [6,40,96,144,288] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,288] 13 (by decide) (choices 1) [1,64,128] r7511 c7511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1190
  · exact u1191
  · exact u1192

def r7512 : Route 9 := (fun mask => (mask,id))

def c7512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7512 : Upper (D 8) (R 8) [6,40,96,144,320] 13 := by
  apply FastRouting.sound _ _ [6,40,96,144,320] 13 (by decide) (choices 1) [1,128] r7512 c7512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1193
  · exact u1194

def b7513 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7)], upper := (rows 7 42 100 152 400 97 97 225 353), lower := (rows 7 42 100 152 400 32 64 128 256), losses := [] }

theorem u7513 : Upper (D 8) (R 8) [6,40,96,144,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7513 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7514 : PairBound 9 := { available := 208, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 265 49 240 208 208 464), lower := (rows 7 42 100 265 49 32 64 128 256), losses := [] }

theorem u7514 : Upper (D 8) (R 8) [6,40,96,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7514 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7515 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 265 81 176 240 176 432), lower := (rows 7 42 100 265 81 32 64 128 256), losses := [] }

theorem u7515 : Upper (D 8) (R 8) [6,40,96,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7515 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7516 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 100 265 112 177 209 145 401), lower := (rows 7 42 100 265 112 32 64 128 256), losses := [] }

theorem u7516 : Upper (D 8) (R 8) [6,40,96,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7516 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7517 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 100 265 145 240 240 240 496), lower := (rows 7 42 100 265 145 32 64 128 256), losses := [] }

theorem u7517 : Upper (D 8) (R 8) [6,40,96,257,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7517 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7518 : Route 9 := (fun mask => (mask,id))

def c7518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u7518 : Upper (D 8) (R 8) [6,40,96,257,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,160] 13 (by decide) (choices 1) [1,16,64,128] r7518 c7518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1195
  · exact u1196
  · exact u1197
  · exact u1198

def r7519 : Route 9 := (fun mask => (mask,id))

def c7519 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7519 : Upper (D 8) (R 8) [6,40,96,257,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,257,192] 13 (by decide) (choices 1) [1,16,128] r7519 c7519
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1199
  · exact u1200
  · exact u1201

def b7520 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 280 49 225 193 193 449), lower := (rows 7 42 100 280 49 32 64 128 256), losses := [] }

theorem u7520 : Upper (D 8) (R 8) [6,40,96,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7520 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7521 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 280 81 161 225 161 417), lower := (rows 7 42 100 280 81 32 64 128 256), losses := [] }

theorem u7521 : Upper (D 8) (R 8) [6,40,96,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7521 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7522 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 100 280 112 161 193 129 385), lower := (rows 7 42 100 280 112 32 64 128 256), losses := [] }

theorem u7522 : Upper (D 8) (R 8) [6,40,96,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7522 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7523 : Route 9 := (fun mask => (mask,id))

def c7523 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7523 : Upper (D 8) (R 8) [6,40,96,272,129] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,129] 13 (by decide) (choices 1) [1,64,128] r7523 c7523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1202
  · exact u1203
  · exact u1204

def r7524 : Route 9 := (fun mask => (mask,id))

def c7524 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7524 : Upper (D 8) (R 8) [6,40,96,272,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,160] 13 (by decide) (choices 1) [1,64,128] r7524 c7524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1205
  · exact u1206
  · exact u1207

def r7525 : Route 9 := (fun mask => (mask,id))

def c7525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7525 : Upper (D 8) (R 8) [6,40,96,272,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,192] 13 (by decide) (choices 1) [1,128] r7525 c7525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1208
  · exact u1209

def b7526 : PairBound 9 := { available := 209, camps := [{ cop := 4, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 392 49 241 209 209 465), lower := (rows 7 42 100 392 49 32 64 128 256), losses := [] }

theorem u7526 : Upper (D 8) (R 8) [6,40,96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7526 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7527 : PairBound 9 := { available := 177, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 100 392 81 177 241 177 433), lower := (rows 7 42 100 392 81 32 64 128 256), losses := [] }

theorem u7527 : Upper (D 8) (R 8) [6,40,96,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7527 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7528 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 100 392 112 177 209 145 401), lower := (rows 7 42 100 392 112 32 64 128 256), losses := [] }

theorem u7528 : Upper (D 8) (R 8) [6,40,96,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7528 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7529 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 100, targets := 128 }], pairs := [(2,7)], upper := (rows 7 42 100 392 145 113 113 241 369), lower := (rows 7 42 100 392 145 32 64 128 256), losses := [] }

theorem u7529 : Upper (D 8) (R 8) [6,40,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7529 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7530 : Route 9 := (fun mask => (mask,id))

def c7530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7530 : Upper (D 8) (R 8) [6,40,96,384,160] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,160] 13 (by decide) (choices 1) [1,16,64] r7530 c7530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1210
  · exact u1211
  · exact u1212

def r7531 : Route 9 := (fun mask => (mask,id))

def c7531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u7531 : Upper (D 8) (R 8) [6,40,96,384,192] 13 := by
  apply FastRouting.sound _ _ [6,40,96,384,192] 13 (by decide) (choices 1) [1,16] r7531 c7531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1213
  · exact u1214

def b7532 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 25 49 480 480 480 480), lower := (rows 7 42 196 25 49 32 64 128 256), losses := [] }

theorem u7532 : Upper (D 8) (R 8) [6,40,192,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7532 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7533 : PairBound 9 := { available := 416, camps := [{ cop := 3, region := 418, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 196 25 81 416 480 416 416), lower := (rows 7 42 196 25 81 32 64 128 256), losses := [] }

theorem u7533 : Upper (D 8) (R 8) [6,40,192,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7533 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7534 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 418, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 25 112 417 481 417 417), lower := (rows 7 42 196 25 112 32 64 128 256), losses := [] }

theorem u7534 : Upper (D 8) (R 8) [6,40,192,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7534 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7535 : PairBound 9 := { available := 289, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 25 208 289 353 417 289), lower := (rows 7 42 196 25 208 32 64 128 256), losses := [] }

theorem u7535 : Upper (D 8) (R 8) [6,40,192,17,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7535 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7536 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 196 25 273 224 224 224 480), lower := (rows 7 42 196 25 273 32 64 128 256), losses := [] }

theorem u7536 : Upper (D 8) (R 8) [6,40,192,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7536 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7537 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7537 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7537 : Upper (D 8) (R 8) [6,40,192,17,288] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,288] 13 (by decide) (choices 1) [1,64] r7537 c7537
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1215
  · exact u1216

def b7538 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 25 336 161 225 161 417), lower := (rows 7 42 196 25 336 32 64 128 256), losses := [] }

theorem u7538 : Upper (D 8) (R 8) [6,40,192,17,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7538 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7539 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 42 196 265 49 240 240 240 496), lower := (rows 7 42 196 265 49 32 64 128 256), losses := [] }

theorem u7539 : Upper (D 8) (R 8) [6,40,192,257,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7539 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7540 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 265 81 176 240 176 432), lower := (rows 7 42 196 265 81 32 64 128 256), losses := [] }

theorem u7540 : Upper (D 8) (R 8) [6,40,192,257,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7540 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7541 : Route 9 := (fun mask => (mask,id))

def c7541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7541 : Upper (D 8) (R 8) [6,40,192,257,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257,96] 13 (by decide) (choices 1) [1,16,128] r7541 c7541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1217
  · exact u1218
  · exact u1219

def b7542 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 265 208 49 113 177 305), lower := (rows 7 42 196 265 208 32 64 128 256), losses := [] }

theorem u7542 : Upper (D 8) (R 8) [6,40,192,257,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7542 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7543 : Route 9 := (fun mask => match mask with | 128 => (64,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7543 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7543 : Upper (D 8) (R 8) [6,40,192,272,33] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,33] 13 (by decide) (choices 1) [1,64] r7543 c7543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1220
  · exact u1221

def b7544 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 426, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 196 280 81 161 225 161 417), lower := (rows 7 42 196 280 81 32 64 128 256), losses := [] }

theorem u7544 : Upper (D 8) (R 8) [6,40,192,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7544 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7545 : Route 9 := (fun mask => (mask,id))

def c7545 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7545 : Upper (D 8) (R 8) [6,40,192,272,96] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272,96] 13 (by decide) (choices 1) [1,128] r7545 c7545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1222
  · exact u1223

def b7546 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 280 208 33 97 161 289), lower := (rows 7 42 196 280 208 32 64 128 256), losses := [] }

theorem u7546 : Upper (D 8) (R 8) [6,40,192,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7546 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7547 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 88 49 224 224 224 480), lower := (rows 7 42 261 88 49 32 64 128 256), losses := [] }

theorem u7547 : Upper (D 8) (R 8) [6,40,257,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7547 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7548 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 81 160 224 160 416), lower := (rows 7 42 261 88 81 32 64 128 256), losses := [] }

theorem u7548 : Upper (D 8) (R 8) [6,40,257,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7548 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7549 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 88 112 161 225 161 417), lower := (rows 7 42 261 88 112 32 64 128 256), losses := [] }

theorem u7549 : Upper (D 8) (R 8) [6,40,257,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7549 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7550 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 88 145 224 224 224 480), lower := (rows 7 42 261 88 145 32 64 128 256), losses := [] }

theorem u7550 : Upper (D 8) (R 8) [6,40,257,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7550 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7551 : Route 9 := (fun mask => (mask,id))

def c7551 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u7551 : Upper (D 8) (R 8) [6,40,257,80,160] 13 := by
  apply FastRouting.sound _ _ [6,40,257,80,160] 13 (by decide) (choices 1) [1,64,128] r7551 c7551
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1224
  · exact u1225
  · exact u1226

def b7552 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 7 42 261 88 208 161 225 161 417), lower := (rows 7 42 261 88 208 32 64 128 256), losses := [] }

theorem u7552 : Upper (D 8) (R 8) [6,40,257,80,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7552 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7553 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 202, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 200 49 240 240 240 496), lower := (rows 7 42 261 200 49 32 64 128 256), losses := [] }

theorem u7553 : Upper (D 8) (R 8) [6,40,257,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7553 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7554 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 170, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 261 200 81 176 240 176 432), lower := (rows 7 42 261 200 81 32 64 128 256), losses := [] }

theorem u7554 : Upper (D 8) (R 8) [6,40,257,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7554 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r7555 : Route 9 := (fun mask => (mask,id))

def c7555 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u7555 : Upper (D 8) (R 8) [6,40,257,192,96] 13 := by
  apply FastRouting.sound _ _ [6,40,257,192,96] 13 (by decide) (choices 1) [1,16,128] r7555 c7555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1227
  · exact u1228
  · exact u1229

def b7556 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 261 200 208 49 113 177 305), lower := (rows 7 42 261 200 208 32 64 128 256), losses := [] }

theorem u7556 : Upper (D 8) (R 8) [6,40,257,192,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7556 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7557 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0)], upper := (rows 7 42 276 73 49 224 224 224 480), lower := (rows 7 42 276 73 49 32 64 128 256), losses := [] }

theorem u7557 : Upper (D 8) (R 8) [6,40,272,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7557 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7558 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 16, targets := 32 }], pairs := [(4,5)], upper := (rows 7 42 276 73 81 160 224 160 416), lower := (rows 7 42 276 73 81 32 64 128 256), losses := [] }

theorem u7558 : Upper (D 8) (R 8) [6,40,272,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7558 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b7559 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 7 42 276 73 112 161 225 161 417), lower := (rows 7 42 276 73 112 32 64 128 256), losses := [] }

theorem u7559 : Upper (D 8) (R 8) [6,40,272,65,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b7559 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u7559
end Delivery.IrregularNine14.P08
