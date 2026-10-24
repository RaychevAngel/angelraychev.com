import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0102
import IrregularNine14P09C0103
import IrregularNine14P09C0104

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r8460 : Route 9 := (fun mask => (mask,id))

def c8460 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8460 : Upper (D 9) (R 9) [96,12,129,160,66] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,66] 13 (by decide) (choices 1) [1,16,256] r8460 c8460
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6129
  · exact u6130
  · exact u6131

def r8461 : Route 9 := (fun mask => (mask,id))

def c8461 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8461 : Upper (D 9) (R 9) [96,12,129,160,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,257] 13 (by decide) (choices 1) [2,16,64,256] r8461 c8461
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6132
  · exact u6133
  · exact u6134
  · exact u6135

def r8462 : Route 9 := (fun mask => (mask,id))

def c8462 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8462 : Upper (D 9) (R 9) [96,12,129,160,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,258] 13 (by decide) (choices 1) [1,16,64,256] r8462 c8462
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6136
  · exact u6137
  · exact u6138
  · exact u6139

def r8463 : Route 9 := (fun mask => (mask,id))

def c8463 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8463 : Upper (D 9) (R 9) [96,12,129,160,320] 13 := by
  apply FastRouting.sound _ _ [96,12,129,160,320] 13 (by decide) (choices 1) [1,2,16,256] r8463 c8463
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6140
  · exact u6141
  · exact u6142
  · exact u6143

theorem m8464_256 : Upper (D 9) (R 9) [96,12,129,257,34,256] 13 :=
  permutation_upper _ _ _ [96,12,129,257,34,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6146

def r8464 : Route 9 := (fun mask => (mask,id))

def c8464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u8464 : Upper (D 9) (R 9) [96,12,129,257,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,34] 13 (by decide) (choices 1) [16,64,128,256] r8464 c8464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6144
  · exact u6145
  · exact u6146
  · exact m8464_256

def b8465 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 133 265 112 434 466 402 402), lower := (rows 97 14 133 265 112 32 64 128 256), losses := [] }

theorem u8465 : Upper (D 9) (R 9) [96,12,129,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8466 : Route 9 := (fun mask => (mask,id))

def c8466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8466 : Upper (D 9) (R 9) [96,12,129,257,130] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,130] 13 (by decide) (choices 1) [16,64,256] r8466 c8466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6147
  · exact u6148
  · exact u6149

def r8467 : Route 9 := (fun mask => (mask,id))

def c8467 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8467 : Upper (D 9) (R 9) [96,12,129,257,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,160] 13 (by decide) (choices 1) [2,16,64,256] r8467 c8467
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6150
  · exact u6151
  · exact u6152
  · exact u6153

def r8468 : Route 9 := (fun mask => (mask,id))

def c8468 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8468 : Upper (D 9) (R 9) [96,12,129,257,384] 13 := by
  apply FastRouting.sound _ _ [96,12,129,257,384] 13 (by decide) (choices 1) [2,16,64] r8468 c8468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6154
  · exact u6155
  · exact u6156

def b8469 : PairBound 9 := { available := 464, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 133 266 49 496 464 464 464), lower := (rows 97 14 133 266 49 32 64 128 256), losses := [] }

theorem u8469 : Upper (D 9) (R 9) [96,12,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8469 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8470 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 133 266 112 433 465 401 401), lower := (rows 97 14 133 266 112 32 64 128 256), losses := [] }

theorem u8470 : Upper (D 9) (R 9) [96,12,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8470 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8471 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 97 14 133 266 145 368 368 496 368), lower := (rows 97 14 133 266 145 32 64 128 256), losses := [] }

theorem u8471 : Upper (D 9) (R 9) [96,12,129,258,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8471 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8472 : Route 9 := (fun mask => (mask,id))

def c8472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8472 : Upper (D 9) (R 9) [96,12,129,258,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258,160] 13 (by decide) (choices 1) [1,16,64,256] r8472 c8472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6157
  · exact u6158
  · exact u6159
  · exact u6160

def r8473 : Route 9 := (fun mask => (mask,id))

def c8473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8473 : Upper (D 9) (R 9) [96,12,129,258,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258,257] 13 (by decide) (choices 1) [16,64,128] r8473 c8473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6161
  · exact u6162
  · exact u6163

def r8474 : Route 9 := (fun mask => (mask,id))

def c8474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8474 : Upper (D 9) (R 9) [96,12,129,258,288] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258,288] 13 (by decide) (choices 1) [1,16,64,128] r8474 c8474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6164
  · exact u6165
  · exact u6166
  · exact u6167

def r8475 : Route 9 := (fun mask => (mask,id))

def c8475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8475 : Upper (D 9) (R 9) [96,12,129,258,384] 13 := by
  apply FastRouting.sound _ _ [96,12,129,258,384] 13 (by decide) (choices 1) [1,16,64] r8475 c8475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6168
  · exact u6169
  · exact u6170

def b8476 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 133 280 49 482 450 450 450), lower := (rows 97 14 133 280 49 32 64 128 256), losses := [] }

theorem u8476 : Upper (D 9) (R 9) [96,12,129,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8476 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8477 : Route 9 := (fun mask => (mask,id))

def c8477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u8477 : Upper (D 9) (R 9) [96,12,129,272,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,34] 13 (by decide) (choices 1) [1,64,128,256] r8477 c8477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6171
  · exact u6172
  · exact u6173
  · exact u6174

def b8478 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 133 280 112 419 451 387 387), lower := (rows 97 14 133 280 112 32 64 128 256), losses := [] }

theorem u8478 : Upper (D 9) (R 9) [96,12,129,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8479 : PairBound 9 := { available := 354, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 97 14 133 280 145 354 354 482 354), lower := (rows 97 14 133 280 145 32 64 128 256), losses := [] }

theorem u8479 : Upper (D 9) (R 9) [96,12,129,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8479 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8480 : Route 9 := (fun mask => (mask,id))

def c8480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8480 : Upper (D 9) (R 9) [96,12,129,272,130] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,130] 13 (by decide) (choices 1) [1,64,256] r8480 c8480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6175
  · exact u6176
  · exact u6177

def r8481 : Route 9 := (fun mask => (mask,id))

def c8481 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8481 : Upper (D 9) (R 9) [96,12,129,272,160] 13 := by
  apply FastRouting.sound _ _ [96,12,129,272,160] 13 (by decide) (choices 1) [1,2,64,256] r8481 c8481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6178
  · exact u6179
  · exact u6180
  · exact u6181

def b8482 : PairBound 9 := { available := 226, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 133 280 273 226 226 226 482), lower := (rows 97 14 133 280 273 32 64 128 256), losses := [] }

theorem u8482 : Upper (D 9) (R 9) [96,12,129,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8482 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8483 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 133 280 274 225 225 225 481), lower := (rows 97 14 133 280 274 32 64 128 256), losses := [] }

theorem u8483 : Upper (D 9) (R 9) [96,12,129,272,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8483 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8484 : PairBound 9 := { available := 195, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 133 280 304 227 195 195 451), lower := (rows 97 14 133 280 304 32 64 128 256), losses := [] }

theorem u8484 : Upper (D 9) (R 9) [96,12,129,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8484 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8485 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 133 280 400 99 99 227 355), lower := (rows 97 14 133 280 400 32 64 128 256), losses := [] }

theorem u8485 : Upper (D 9) (R 9) [96,12,129,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8485 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8486 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 16, targets := 416 },{ cop := 4, region := 430, targets := 64 }], pairs := [(1,6),(2,6),(4,5),(4,7),(4,8)], upper := (rows 97 14 133 296 81 434 466 402 402), lower := (rows 97 14 133 296 81 32 64 128 256), losses := [] }

theorem u8486 : Upper (D 9) (R 9) [96,12,129,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8486 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8487 : Route 9 := (fun mask => (mask,id))

def c8487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u8487 : Upper (D 9) (R 9) [96,12,129,288,66] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,66] 13 (by decide) (choices 1) [1,16,128,256] r8487 c8487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6182
  · exact u6183
  · exact u6184
  · exact u6185

def b8488 : PairBound 9 := { available := 338, camps := [{ cop := 2, region := 16, targets := 352 },{ cop := 4, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6),(4,8)], upper := (rows 97 14 133 296 145 370 338 466 338), lower := (rows 97 14 133 296 145 32 64 128 256), losses := [] }

theorem u8488 : Upper (D 9) (R 9) [96,12,129,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8488 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8489 : Route 9 := (fun mask => (mask,id))

def c8489 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8489 : Upper (D 9) (R 9) [96,12,129,288,130] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,130] 13 (by decide) (choices 1) [1,16,64,256] r8489 c8489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6186
  · exact u6187
  · exact u6188
  · exact u6189

def r8490 : Route 9 := (fun mask => (mask,id))

def c8490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8490 : Upper (D 9) (R 9) [96,12,129,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,192] 13 (by decide) (choices 1) [1,2,16,256] r8490 c8490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6190
  · exact u6191
  · exact u6192
  · exact u6193

def r8491 : Route 9 := (fun mask => (mask,id))

def c8491 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8491 : Upper (D 9) (R 9) [96,12,129,288,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,257] 13 (by decide) (choices 1) [2,16,64,128] r8491 c8491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6194
  · exact u6195
  · exact u6196
  · exact u6197

def r8492 : Route 9 := (fun mask => (mask,id))

def c8492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8492 : Upper (D 9) (R 9) [96,12,129,288,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,258] 13 (by decide) (choices 1) [1,16,64,128] r8492 c8492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6198
  · exact u6199
  · exact u6200
  · exact u6201

def r8493 : Route 9 := (fun mask => (mask,id))

def c8493 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8493 : Upper (D 9) (R 9) [96,12,129,288,320] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,320] 13 (by decide) (choices 1) [1,2,16,128] r8493 c8493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6202
  · exact u6203
  · exact u6204
  · exact u6205

def r8494 : Route 9 := (fun mask => (mask,id))

def c8494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8494 : Upper (D 9) (R 9) [96,12,129,288,384] 13 := by
  apply FastRouting.sound _ _ [96,12,129,288,384] 13 (by decide) (choices 1) [1,2,16,64] r8494 c8494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6206
  · exact u6207
  · exact u6208
  · exact u6209

def b8495 : PairBound 9 := { available := 338, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 133 392 49 370 338 466 338), lower := (rows 97 14 133 392 49 32 64 128 256), losses := [] }

theorem u8495 : Upper (D 9) (R 9) [96,12,129,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8495 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8496 : Route 9 := (fun mask => (mask,id))

def c8496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8496 : Upper (D 9) (R 9) [96,12,129,384,34] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,34] 13 (by decide) (choices 1) [1,16,64,256] r8496 c8496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6210
  · exact u6211
  · exact u6212
  · exact u6213

def b8497 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 133 392 112 307 339 403 275), lower := (rows 97 14 133 392 112 32 64 128 256), losses := [] }

theorem u8497 : Upper (D 9) (R 9) [96,12,129,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8497 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8498 : Route 9 := (fun mask => (mask,id))

def c8498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8498 : Upper (D 9) (R 9) [96,12,129,384,257] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,257] 13 (by decide) (choices 1) [2,16,64] r8498 c8498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6214
  · exact u6215
  · exact u6216

def r8499 : Route 9 := (fun mask => (mask,id))

def c8499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8499 : Upper (D 9) (R 9) [96,12,129,384,258] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,258] 13 (by decide) (choices 1) [1,16,64] r8499 c8499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6217
  · exact u6218
  · exact u6219

def r8500 : Route 9 := (fun mask => (mask,id))

def c8500 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8500 : Upper (D 9) (R 9) [96,12,129,384,288] 13 := by
  apply FastRouting.sound _ _ [96,12,129,384,288] 13 (by decide) (choices 1) [1,2,16,64] r8500 c8500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6220
  · exact u6221
  · exact u6222
  · exact u6223

def b8501 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 152 273 353 353 481 353), lower := (rows 97 14 134 152 273 32 64 128 256), losses := [] }

theorem u8501 : Upper (D 9) (R 9) [96,12,130,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8501 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8502 : PairBound 9 := { available := 321, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 152 304 353 321 449 321), lower := (rows 97 14 134 152 304 32 64 128 256), losses := [] }

theorem u8502 : Upper (D 9) (R 9) [96,12,130,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8502 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8503 : PairBound 9 := { available := 337, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 168 273 369 337 465 337), lower := (rows 97 14 134 168 273 32 64 128 256), losses := [] }

theorem u8503 : Upper (D 9) (R 9) [96,12,130,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8503 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8504 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 168 336 305 337 401 273), lower := (rows 97 14 134 168 336 32 64 128 256), losses := [] }

theorem u8504 : Upper (D 9) (R 9) [96,12,130,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8504 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8505 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 16, targets := 448 },{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(4,6),(4,7),(4,8)], upper := (rows 97 14 134 280 49 481 449 449 449), lower := (rows 97 14 134 280 49 32 64 128 256), losses := [] }

theorem u8505 : Upper (D 9) (R 9) [96,12,130,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8505 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8506 : PairBound 9 := { available := 385, camps := [{ cop := 0, region := 16, targets := 384 },{ cop := 4, region := 1, targets := 384 },{ cop := 0, region := 16, targets := 1 }], pairs := [(0,7),(0,8),(4,0),(4,7),(4,8)], upper := (rows 97 14 134 280 112 417 449 385 385), lower := (rows 97 14 134 280 112 32 64 128 256), losses := [] }

theorem u8506 : Upper (D 9) (R 9) [96,12,130,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8506 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8507 : Route 9 := (fun mask => (mask,id))

def c8507 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8507 : Upper (D 9) (R 9) [96,12,130,272,129] 13 := by
  apply FastRouting.sound _ _ [96,12,130,272,129] 13 (by decide) (choices 1) [1,64,256] r8507 c8507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6224
  · exact u6225
  · exact u6226

def r8508 : Route 9 := (fun mask => (mask,id))

def c8508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u8508 : Upper (D 9) (R 9) [96,12,130,272,160] 13 := by
  apply FastRouting.sound _ _ [96,12,130,272,160] 13 (by decide) (choices 1) [1,64,256] r8508 c8508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6227
  · exact u6228
  · exact u6229

def b8509 : PairBound 9 := { available := 225, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 134 280 273 225 225 225 481), lower := (rows 97 14 134 280 273 32 64 128 256), losses := [] }

theorem u8509 : Upper (D 9) (R 9) [96,12,130,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8509 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8510 : PairBound 9 := { available := 193, camps := [{ cop := 4, region := 8, targets := 225 },{ cop := 3, region := 225, targets := 256 }], pairs := [(0,8),(3,0),(3,5),(3,6),(3,7)], upper := (rows 97 14 134 280 304 225 193 193 449), lower := (rows 97 14 134 280 304 32 64 128 256), losses := [] }

theorem u8510 : Upper (D 9) (R 9) [96,12,130,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8510 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8511 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 14, targets := 97 }], pairs := [(1,0),(1,5),(1,6),(2,0),(2,5)], upper := (rows 97 14 134 280 400 97 97 225 353), lower := (rows 97 14 134 280 400 32 64 128 256), losses := [] }

theorem u8511 : Upper (D 9) (R 9) [96,12,130,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8511 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8512 : PairBound 9 := { available := 401, camps := [{ cop := 4, region := 430, targets := 64 },{ cop := 0, region := 16, targets := 384 }], pairs := [(1,6),(2,6),(3,6),(4,7),(4,8)], upper := (rows 97 14 134 296 81 433 465 401 401), lower := (rows 97 14 134 296 81 32 64 128 256), losses := [] }

theorem u8512 : Upper (D 9) (R 9) [96,12,130,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8512 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r8513 : Route 9 := (fun mask => (mask,id))

def c8513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u8513 : Upper (D 9) (R 9) [96,12,130,288,129] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,129] 13 (by decide) (choices 1) [1,16,64,256] r8513 c8513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6230
  · exact u6231
  · exact u6232
  · exact u6233

def r8514 : Route 9 := (fun mask => (mask,id))

def c8514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u8514 : Upper (D 9) (R 9) [96,12,130,288,192] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,192] 13 (by decide) (choices 1) [1,16,256] r8514 c8514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6234
  · exact u6235
  · exact u6236

def r8515 : Route 9 := (fun mask => (mask,id))

def c8515 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u8515 : Upper (D 9) (R 9) [96,12,130,288,257] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,257] 13 (by decide) (choices 1) [1,16,64,128] r8515 c8515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u6237
  · exact u6238
  · exact u6239
  · exact u6240

def r8516 : Route 9 := (fun mask => (mask,id))

def c8516 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u8516 : Upper (D 9) (R 9) [96,12,130,288,320] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,320] 13 (by decide) (choices 1) [1,16,128] r8516 c8516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6241
  · exact u6242
  · exact u6243

def r8517 : Route 9 := (fun mask => (mask,id))

def c8517 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u8517 : Upper (D 9) (R 9) [96,12,130,288,384] 13 := by
  apply FastRouting.sound _ _ [96,12,130,288,384] 13 (by decide) (choices 1) [1,16,64] r8517 c8517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u6244
  · exact u6245
  · exact u6246

def b8518 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 392 273 113 113 241 369), lower := (rows 97 14 134 392 273 32 64 128 256), losses := [] }

theorem u8518 : Upper (D 9) (R 9) [96,12,130,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8518 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b8519 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 6, targets := 353 }], pairs := [(1,0),(1,5),(1,6),(1,8),(2,0)], upper := (rows 97 14 134 392 304 113 81 209 337), lower := (rows 97 14 134 392 304 32 64 128 256), losses := [] }

theorem u8519 : Upper (D 9) (R 9) [96,12,130,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b8519 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u8519
end Delivery.IrregularNine14.P09
