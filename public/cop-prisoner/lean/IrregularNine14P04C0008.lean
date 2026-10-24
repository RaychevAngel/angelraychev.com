import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0002
import IrregularNine14P04C0003

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r480 : Route 9 := (fun mask => (mask,id))

def c480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u480 : Upper (D 4) (R 4) [6,33,72,384,10] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384,10] 13 (by decide) (choices 1) [1,4,16] r480 c480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u163
  · exact u164
  · exact u165

def b481 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 35 76 392 28 51 83 147 275), lower := (rows 7 35 76 392 28 32 64 128 256), losses := [] }

theorem u481 : Upper (D 4) (R 4) [6,33,72,384,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b481
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b482 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 14 273 56 88 152 280), lower := (rows 7 35 196 14 273 32 64 128 256), losses := [] }

theorem u482 : Upper (D 4) (R 4) [6,33,192,6,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b482
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b483 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 14 280 57 89 153 281), lower := (rows 7 35 196 14 280 32 64 128 256), losses := [] }

theorem u483 : Upper (D 4) (R 4) [6,33,192,6,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b483
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b484 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 196, targets := 1 }], pairs := [(2,0)], upper := (rows 7 35 196 26 273 60 92 156 284), lower := (rows 7 35 196 26 273 32 64 128 256), losses := [] }

theorem u484 : Upper (D 4) (R 4) [6,33,192,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b484
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r485 : Route 9 := (fun mask => (mask,id))

def c485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u485 : Upper (D 4) (R 4) [6,33,192,18,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18,260] 13 (by decide) (choices 1) [1,8,16] r485 c485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u166
  · exact u167
  · exact u168

def r486 : Route 9 := (fun mask => (mask,id))

def c486 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u486 : Upper (D 4) (R 4) [6,33,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,257] 13 (by decide) (choices 1) [2,8,16] r486 c486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u169
  · exact u170
  · exact u171

def r487 : Route 9 := (fun mask => (mask,id))

def c487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u487 : Upper (D 4) (R 4) [6,33,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,258] 13 (by decide) (choices 1) [1,8,16] r487 c487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u172
  · exact u173
  · exact u174

def r488 : Route 9 := (fun mask => (mask,id))

def c488 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u488 : Upper (D 4) (R 4) [6,33,192,20,264] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20,264] 13 (by decide) (choices 1) [1,2,8,16] r488 c488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u175
  · exact u176
  · exact u177
  · exact u178

def b489 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 137 280 57 89 153 281), lower := (rows 7 38 70 137 280 32 64 128 256), losses := [] }

theorem u489 : Upper (D 4) (R 4) [6,36,66,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b489
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b490 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 152 280 57 89 153 281), lower := (rows 7 38 70 152 280 32 64 128 256), losses := [] }

theorem u490 : Upper (D 4) (R 4) [6,36,66,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b490
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b491 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 26 145 313 345 409 281), lower := (rows 7 38 76 26 145 32 64 128 256), losses := [] }

theorem u491 : Upper (D 4) (R 4) [6,36,72,18,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b491
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b492 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 26 400 57 89 153 281), lower := (rows 7 38 76 26 400 32 64 128 256), losses := [] }

theorem u492 : Upper (D 4) (R 4) [6,36,72,18,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b492
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b493 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 137 26 305 337 401 273), lower := (rows 7 38 76 137 26 32 64 128 256), losses := [] }

theorem u493 : Upper (D 4) (R 4) [6,36,72,129,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b493
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b494 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 137 274 57 89 153 281), lower := (rows 7 38 76 137 274 32 64 128 256), losses := [] }

theorem u494 : Upper (D 4) (R 4) [6,36,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b494
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b495 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 137 280 51 83 147 275), lower := (rows 7 38 76 137 280 32 64 128 256), losses := [] }

theorem u495 : Upper (D 4) (R 4) [6,36,72,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b495
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b496 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 138 273 57 89 153 281), lower := (rows 7 38 76 138 273 32 64 128 256), losses := [] }

theorem u496 : Upper (D 4) (R 4) [6,36,72,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b496
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b497 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 138 280 49 81 145 273), lower := (rows 7 38 76 138 280 32 64 128 256), losses := [] }

theorem u497 : Upper (D 4) (R 4) [6,36,72,130,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b497
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b498 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 152 273 59 91 155 283), lower := (rows 7 38 76 152 273 32 64 128 256), losses := [] }

theorem u498 : Upper (D 4) (R 4) [6,36,72,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b498
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b499 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 152 274 57 89 153 281), lower := (rows 7 38 76 152 274 32 64 128 256), losses := [] }

theorem u499 : Upper (D 4) (R 4) [6,36,72,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b499
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b500 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 152 280 51 83 147 275), lower := (rows 7 38 76 152 280 32 64 128 256), losses := [] }

theorem u500 : Upper (D 4) (R 4) [6,36,72,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b500
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b501 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 392 26 49 81 145 273), lower := (rows 7 38 76 392 26 32 64 128 256), losses := [] }

theorem u501 : Upper (D 4) (R 4) [6,36,72,384,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b501
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b502 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 196 26 273 57 89 153 281), lower := (rows 7 38 196 26 273 32 64 128 256), losses := [] }

theorem u502 : Upper (D 4) (R 4) [6,36,192,18,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b502
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b503 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 274 53 85 149 277), lower := (rows 7 42 76 137 274 32 64 128 256), losses := [] }

theorem u503 : Upper (D 4) (R 4) [6,40,72,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b503
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b504 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 76 138 273 53 85 149 277), lower := (rows 7 42 76 138 273 32 64 128 256), losses := [] }

theorem u504 : Upper (D 4) (R 4) [6,40,72,130,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b504
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b505 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 76 138 276 49 81 145 273), lower := (rows 7 42 76 138 276 32 64 128 256), losses := [] }

theorem u505 : Upper (D 4) (R 4) [6,40,72,130,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b505
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b506 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 152 273 55 87 151 279), lower := (rows 7 42 76 152 273 32 64 128 256), losses := [] }

theorem u506 : Upper (D 4) (R 4) [6,40,72,144,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b506
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b507 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 152 274 53 85 149 277), lower := (rows 7 42 76 152 274 32 64 128 256), losses := [] }

theorem u507 : Upper (D 4) (R 4) [6,40,72,144,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b507
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r508 : Route 9 := (fun mask => (mask,id))

def c508 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u508 : Upper (D 4) (R 4) [6,40,80,129,257] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,257] 13 (by decide) (choices 1) [2,4,8,16] r508 c508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u179
  · exact u180
  · exact u181
  · exact u182

def r509 : Route 9 := (fun mask => (mask,id))

def c509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u509 : Upper (D 4) (R 4) [6,40,80,129,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,258] 13 (by decide) (choices 1) [1,4,8,16] r509 c509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u183
  · exact u184
  · exact u185
  · exact u186

def r510 : Route 9 := (fun mask => (mask,id))

def c510 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u510 : Upper (D 4) (R 4) [6,40,80,129,260] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,260] 13 (by decide) (choices 1) [1,2,8,16] r510 c510
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u187
  · exact u188
  · exact u189
  · exact u190

def r511 : Route 9 := (fun mask => (mask,id))

def c511 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u511 : Upper (D 4) (R 4) [6,40,80,129,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,264] 13 (by decide) (choices 1) [1,2,4,16] r511 c511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u191
  · exact u192
  · exact u193
  · exact u194

def r512 : Route 9 := (fun mask => (mask,id))

def c512 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u512 : Upper (D 4) (R 4) [6,40,80,130,260] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,260] 13 (by decide) (choices 1) [1,8,16] r512 c512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u195
  · exact u196
  · exact u197

def r513 : Route 9 := (fun mask => (mask,id))

def c513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u513 : Upper (D 4) (R 4) [6,40,80,130,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,264] 13 (by decide) (choices 1) [1,4,16] r513 c513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u198
  · exact u199
  · exact u200

def r514 : Route 9 := (fun mask => (mask,id))

def c514 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u514 : Upper (D 4) (R 4) [6,40,80,132,258] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,258] 13 (by decide) (choices 1) [1,8,16] r514 c514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u201
  · exact u202
  · exact u203

def r515 : Route 9 := (fun mask => (mask,id))

def c515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u515 : Upper (D 4) (R 4) [6,40,80,132,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132,264] 13 (by decide) (choices 1) [1,2,16] r515 c515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u204
  · exact u205
  · exact u206

def r516 : Route 9 := (fun mask => (mask,id))

def c516 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u516 : Upper (D 4) (R 4) [6,40,80,144,264] 13 := by
  apply FastRouting.sound _ _ [6,40,80,144,264] 13 (by decide) (choices 1) [1,2,4] r516 c516
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u207
  · exact u208
  · exact u209

def r517 : Route 9 := (fun mask => (mask,id))

def c517 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u517 : Upper (D 4) (R 4) [6,40,192,20,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,257] 13 (by decide) (choices 1) [1,2,8,16] r517 c517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u210
  · exact u211
  · exact u212
  · exact u213

def r518 : Route 9 := (fun mask => (mask,id))

def c518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u518 : Upper (D 4) (R 4) [6,40,192,20,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20,258] 13 (by decide) (choices 1) [1,8,16] r518 c518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u214
  · exact u215
  · exact u216

def b519 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 16, targets := 1 }], pairs := [(4,0)], upper := (rows 7 42 196 265 22 57 89 153 281), lower := (rows 7 42 196 265 22 32 64 128 256), losses := [] }

theorem u519 : Upper (D 4) (R 4) [6,40,192,257,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b519
    (constants 4).1 (constants 4).2 (by decide +kernel)

def r520 : Route 9 := (fun mask => (mask,id))

def c520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u520 : Upper (D 4) (R 4) [6,40,192,258,12] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258,12] 13 (by decide) (choices 1) [1,16] r520 c520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u217
  · exact u218

def b521 : PairBound 9 := { available := 474, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 56 474 506 474 474 474), lower := (rows 7 7 13 56 16 32 64 128 256), losses := [] }

theorem u521 : Upper (D 4) (R 4) [6,5,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b521
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b522 : PairBound 9 := { available := 410, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 13 104 410 442 474 410 410), lower := (rows 7 7 13 104 16 32 64 128 256), losses := [] }

theorem u522 : Upper (D 4) (R 4) [6,5,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b522
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b523 : PairBound 9 := { available := 410, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 7 21 104 410 442 474 410 410), lower := (rows 7 7 21 104 16 32 64 128 256), losses := [] }

theorem u523 : Upper (D 4) (R 4) [6,5,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b523
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b524 : PairBound 9 := { available := 474, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 41 474 506 474 474 474), lower := (rows 7 7 28 41 16 32 64 128 256), losses := [] }

theorem u524 : Upper (D 4) (R 4) [6,5,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b524
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b525 : PairBound 9 := { available := 411, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 28 104 411 443 475 411 411), lower := (rows 7 7 28 104 16 32 64 128 256), losses := [] }

theorem u525 : Upper (D 4) (R 4) [6,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b525
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b526 : PairBound 9 := { available := 282, camps := [{ cop := 5, region := 7, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 37 200 282 314 346 410 282), lower := (rows 7 7 37 200 16 32 64 128 256), losses := [] }

theorem u526 : Upper (D 4) (R 4) [6,5,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b526
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b527 : PairBound 9 := { available := 410, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 73 410 442 474 410 410), lower := (rows 7 7 44 73 16 32 64 128 256), losses := [] }

theorem u527 : Upper (D 4) (R 4) [6,5,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b527
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b528 : PairBound 9 := { available := 283, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 44 200 283 315 347 411 283), lower := (rows 7 7 44 200 16 32 64 128 256), losses := [] }

theorem u528 : Upper (D 4) (R 4) [6,5,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b528
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b529 : PairBound 9 := { available := 410, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 52 73 410 442 474 410 410), lower := (rows 7 7 52 73 16 32 64 128 256), losses := [] }

theorem u529 : Upper (D 4) (R 4) [6,5,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b529
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b530 : PairBound 9 := { available := 283, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 52 200 283 315 347 411 283), lower := (rows 7 7 52 200 16 32 64 128 256), losses := [] }

theorem u530 : Upper (D 4) (R 4) [6,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b530
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b531 : PairBound 9 := { available := 282, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 137 282 314 346 410 282), lower := (rows 7 7 100 137 16 32 64 128 256), losses := [] }

theorem u531 : Upper (D 4) (R 4) [6,5,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b531
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b532 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 392 27 59 91 155 283), lower := (rows 7 7 100 392 16 32 64 128 256), losses := [] }

theorem u532 : Upper (D 4) (R 4) [6,5,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b532
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b533 : PairBound 9 := { available := 470, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 56 470 502 470 470 470), lower := (rows 7 11 13 56 16 32 64 128 256), losses := [] }

theorem u533 : Upper (D 4) (R 4) [6,9,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b533
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b534 : PairBound 9 := { available := 406, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 104 406 438 470 406 406), lower := (rows 7 11 13 104 16 32 64 128 256), losses := [] }

theorem u534 : Upper (D 4) (R 4) [6,9,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b534
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b535 : PairBound 9 := { available := 469, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 56 469 501 469 469 469), lower := (rows 7 11 14 56 16 32 64 128 256), losses := [] }

theorem u535 : Upper (D 4) (R 4) [6,9,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b535
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b536 : PairBound 9 := { available := 405, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 104 405 437 469 405 405), lower := (rows 7 11 14 104 16 32 64 128 256), losses := [] }

theorem u536 : Upper (D 4) (R 4) [6,9,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b536
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b537 : PairBound 9 := { available := 462, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 56 478 494 462 462 462), lower := (rows 7 11 21 56 16 32 64 128 256), losses := [] }

theorem u537 : Upper (D 4) (R 4) [6,9,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b537
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b538 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 414 446 478 414 414), lower := (rows 7 11 21 104 16 32 64 128 256), losses := [] }

theorem u538 : Upper (D 4) (R 4) [6,9,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b538
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b539 : PairBound 9 := { available := 461, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 56 477 493 461 461 461), lower := (rows 7 11 22 56 16 32 64 128 256), losses := [] }

theorem u539 : Upper (D 4) (R 4) [6,9,18,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b539
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u539
end Delivery.IrregularNine14.P04
