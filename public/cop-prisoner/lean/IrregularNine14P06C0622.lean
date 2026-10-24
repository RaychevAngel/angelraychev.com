import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0374
import IrregularNine14P06C0375
import IrregularNine14P06C0376

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b37320 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 262 28 49 108 76 204 332), lower := (rows 35 131 262 28 49 32 64 128 256), losses := [] }

theorem u37320 : Upper (D 6) (R 6) [34,129,258,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37320 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37321 : PairBound 9 := { available := 73, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 262 28 52 105 73 201 329), lower := (rows 35 131 262 28 52 32 64 128 256), losses := [] }

theorem u37321 : Upper (D 6) (R 6) [34,129,258,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37321 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37322 : Route 9 := (fun mask => (mask,id))

def c37322 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37322 : Upper (D 6) (R 6) [34,129,258,20,40] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,40] 13 (by decide) (choices 1) [1,4,64] r37322 c37322
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22447
  · exact u22448
  · exact u22449

def r37323 : Route 9 := (fun mask => (mask,id))

def c37323 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37323 : Upper (D 6) (R 6) [34,129,258,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,65] 13 (by decide) (choices 1) [4,8,64] r37323 c37323
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22450
  · exact u22451
  · exact u22452

def b37324 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 262 28 84 105 105 233 361), lower := (rows 35 131 262 28 84 32 64 128 256), losses := [] }

theorem u37324 : Upper (D 6) (R 6) [34,129,258,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37324 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37325 : Route 9 := (fun mask => (mask,id))

def c37325 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37325 : Upper (D 6) (R 6) [34,129,258,20,72] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,72] 13 (by decide) (choices 1) [1,4,64] r37325 c37325
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22453
  · exact u22454
  · exact u22455

def r37326 : Route 9 := (fun mask => (mask,id))

def c37326 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37326 : Upper (D 6) (R 6) [34,129,258,20,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,20,96] 13 (by decide) (choices 1) [1,4,8,64] r37326 c37326
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22456
  · exact u22457
  · exact u22458
  · exact u22459

def b37327 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 262 41 84 124 92 220 348), lower := (rows 35 131 262 41 84 32 64 128 256), losses := [] }

theorem u37327 : Upper (D 6) (R 6) [34,129,258,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37327 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37328 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 262 41 88 116 84 212 340), lower := (rows 35 131 262 41 88 32 64 128 256), losses := [] }

theorem u37328 : Upper (D 6) (R 6) [34,129,258,33,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37328 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37329 : Route 9 := (fun mask => (mask,id))

def c37329 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37329 : Upper (D 6) (R 6) [34,129,258,36,65] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,65] 13 (by decide) (choices 1) [4,8,16,64] r37329 c37329
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22460
  · exact u22461
  · exact u22462
  · exact u22463

def r37330 : Route 9 := (fun mask => (mask,id))

def c37330 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37330 : Upper (D 6) (R 6) [34,129,258,36,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,68] 13 (by decide) (choices 1) [1,8,16,64] r37330 c37330
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22464
  · exact u22465
  · exact u22466
  · exact u22467

def r37331 : Route 9 := (fun mask => (mask,id))

def c37331 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37331 : Upper (D 6) (R 6) [34,129,258,36,72] 13 := by
  apply FastRouting.sound _ _ [34,129,258,36,72] 13 (by decide) (choices 1) [1,4,16,64] r37331 c37331
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22468
  · exact u22469
  · exact u22470
  · exact u22471

def r37332 : Route 9 := (fun mask => (mask,id))

def c37332 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37332 : Upper (D 6) (R 6) [34,129,258,48,65] 13 := by
  apply FastRouting.sound _ _ [34,129,258,48,65] 13 (by decide) (choices 1) [4,8,64] r37332 c37332
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22472
  · exact u22473
  · exact u22474

def r37333 : Route 9 := (fun mask => (mask,id))

def c37333 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37333 : Upper (D 6) (R 6) [34,129,258,48,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,48,68] 13 (by decide) (choices 1) [1,4,8,64] r37333 c37333
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22475
  · exact u22476
  · exact u22477
  · exact u22478

def r37334 : Route 9 := (fun mask => (mask,id))

def c37334 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37334 : Upper (D 6) (R 6) [34,129,258,48,72] 13 := by
  apply FastRouting.sound _ _ [34,129,258,48,72] 13 (by decide) (choices 1) [1,4,64] r37334 c37334
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22479
  · exact u22480
  · exact u22481

def r37335 : Route 9 := (fun mask => (mask,id))

def c37335 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37335 : Upper (D 6) (R 6) [34,129,258,65,68] 13 := by
  apply FastRouting.sound _ _ [34,129,258,65,68] 13 (by decide) (choices 1) [4,8,16] r37335 c37335
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22482
  · exact u22483
  · exact u22484

def b37336 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 262 73 88 52 116 180 308), lower := (rows 35 131 262 73 88 32 64 128 256), losses := [] }

theorem u37336 : Upper (D 6) (R 6) [34,129,258,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37336 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37337 : Route 9 := (fun mask => (mask,id))

def c37337 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37337 : Upper (D 6) (R 6) [34,129,258,65,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,65,96] 13 (by decide) (choices 1) [4,8,16] r37337 c37337
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22485
  · exact u22486
  · exact u22487

def b37338 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 262 76 84 57 121 185 313), lower := (rows 35 131 262 76 84 32 64 128 256), losses := [] }

theorem u37338 : Upper (D 6) (R 6) [34,129,258,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37338 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37339 : PairBound 9 := { available := 53, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 262 76 88 53 117 181 309), lower := (rows 35 131 262 76 88 32 64 128 256), losses := [] }

theorem u37339 : Upper (D 6) (R 6) [34,129,258,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37339 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37340 : Route 9 := (fun mask => (mask,id))

def c37340 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37340 : Upper (D 6) (R 6) [34,129,258,68,96] 13 := by
  apply FastRouting.sound _ _ [34,129,258,68,96] 13 (by decide) (choices 1) [1,4,8,16] r37340 c37340
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22488
  · exact u22489
  · exact u22490
  · exact u22491

def b37341 : PairBound 9 := { available := 37, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 262 88 88 37 101 165 293), lower := (rows 35 131 262 88 88 32 64 128 256), losses := [] }

theorem u37341 : Upper (D 6) (R 6) [34,129,258,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37341 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37342 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 262 88 112 45 77 141 269), lower := (rows 35 131 262 88 112 32 64 128 256), losses := [] }

theorem u37342 : Upper (D 6) (R 6) [34,129,258,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37342 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37343 : Route 9 := (fun mask => (mask,id))

def c37343 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37343 : Upper (D 6) (R 6) [34,129,264,5,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,6] 13 (by decide) (choices 1) [16,64] r37343 c37343
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22492
  · exact u22493

def b37344 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 268 13 50 116 84 212 340), lower := (rows 35 131 268 13 50 32 64 128 256), losses := [] }

theorem u37344 : Upper (D 6) (R 6) [34,129,264,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37344 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37345 : Route 9 := (fun mask => (mask,id))

def c37345 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37345 : Upper (D 6) (R 6) [34,129,264,5,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,36] 13 (by decide) (choices 1) [2,16,64] r37345 c37345
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22494
  · exact u22495
  · exact u22496

def r37346 : Route 9 := (fun mask => (mask,id))

def c37346 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37346 : Upper (D 6) (R 6) [34,129,264,5,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,66] 13 (by decide) (choices 1) [4,16,64] r37346 c37346
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22497
  · exact u22498
  · exact u22499

def r37347 : Route 9 := (fun mask => (mask,id))

def c37347 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37347 : Upper (D 6) (R 6) [34,129,264,5,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,68] 13 (by decide) (choices 1) [2,16,64] r37347 c37347
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22500
  · exact u22501
  · exact u22502

def r37348 : Route 9 := (fun mask => (mask,id))

def c37348 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37348 : Upper (D 6) (R 6) [34,129,264,5,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,5,96] 13 (by decide) (choices 1) [2,4,16,64] r37348 c37348
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22503
  · exact u22504
  · exact u22505
  · exact u22506

def r37349 : Route 9 := (fun mask => (mask,id))

def c37349 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37349 : Upper (D 6) (R 6) [34,129,264,6,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,5] 13 (by decide) (choices 1) [16,64] r37349 c37349
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22507
  · exact u22508

def b37350 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 268 14 49 116 84 212 340), lower := (rows 35 131 268 14 49 32 64 128 256), losses := [] }

theorem u37350 : Upper (D 6) (R 6) [34,129,264,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37350 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37351 : Route 9 := (fun mask => (mask,id))

def c37351 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37351 : Upper (D 6) (R 6) [34,129,264,6,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,36] 13 (by decide) (choices 1) [1,16,64] r37351 c37351
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22509
  · exact u22510
  · exact u22511

def r37352 : Route 9 := (fun mask => (mask,id))

def c37352 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37352 : Upper (D 6) (R 6) [34,129,264,6,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,65] 13 (by decide) (choices 1) [4,16,64] r37352 c37352
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22512
  · exact u22513
  · exact u22514

def r37353 : Route 9 := (fun mask => (mask,id))

def c37353 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37353 : Upper (D 6) (R 6) [34,129,264,6,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,68] 13 (by decide) (choices 1) [1,16,64] r37353 c37353
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22515
  · exact u22516
  · exact u22517

def r37354 : Route 9 := (fun mask => (mask,id))

def c37354 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37354 : Upper (D 6) (R 6) [34,129,264,6,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,6,96] 13 (by decide) (choices 1) [1,4,16,64] r37354 c37354
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22518
  · exact u22519
  · exact u22520
  · exact u22521

def r37355 : Route 9 := (fun mask => (mask,id))

def c37355 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37355 : Upper (D 6) (R 6) [34,129,264,17,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,6] 13 (by decide) (choices 1) [4,64] r37355 c37355
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22522
  · exact u22523

def b37356 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 268 25 50 100 68 196 324), lower := (rows 35 131 268 25 50 32 64 128 256), losses := [] }

theorem u37356 : Upper (D 6) (R 6) [34,129,264,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37356 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37357 : Route 9 := (fun mask => (mask,id))

def c37357 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37357 : Upper (D 6) (R 6) [34,129,264,17,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,36] 13 (by decide) (choices 1) [2,4,64] r37357 c37357
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22524
  · exact u22525
  · exact u22526

def r37358 : Route 9 := (fun mask => (mask,id))

def c37358 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37358 : Upper (D 6) (R 6) [34,129,264,17,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,66] 13 (by decide) (choices 1) [4,64] r37358 c37358
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22527
  · exact u22528

def r37359 : Route 9 := (fun mask => (mask,id))

def c37359 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37359 : Upper (D 6) (R 6) [34,129,264,17,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,68] 13 (by decide) (choices 1) [2,4,64] r37359 c37359
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22529
  · exact u22530
  · exact u22531

def r37360 : Route 9 := (fun mask => (mask,id))

def c37360 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37360 : Upper (D 6) (R 6) [34,129,264,17,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,17,96] 13 (by decide) (choices 1) [2,4,64] r37360 c37360
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22532
  · exact u22533
  · exact u22534

def r37361 : Route 9 := (fun mask => (mask,id))

def c37361 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37361 : Upper (D 6) (R 6) [34,129,264,18,5] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,5] 13 (by decide) (choices 1) [4,64] r37361 c37361
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22535
  · exact u22536

def b37362 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 268 26 49 100 68 196 324), lower := (rows 35 131 268 26 49 32 64 128 256), losses := [] }

theorem u37362 : Upper (D 6) (R 6) [34,129,264,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37362 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37363 : Route 9 := (fun mask => (mask,id))

def c37363 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37363 : Upper (D 6) (R 6) [34,129,264,18,36] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,36] 13 (by decide) (choices 1) [1,4,64] r37363 c37363
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22537
  · exact u22538
  · exact u22539

def r37364 : Route 9 := (fun mask => (mask,id))

def c37364 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37364 : Upper (D 6) (R 6) [34,129,264,18,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,65] 13 (by decide) (choices 1) [4,64] r37364 c37364
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22540
  · exact u22541

def r37365 : Route 9 := (fun mask => (mask,id))

def c37365 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37365 : Upper (D 6) (R 6) [34,129,264,18,68] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,68] 13 (by decide) (choices 1) [1,4,64] r37365 c37365
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22542
  · exact u22543
  · exact u22544

def r37366 : Route 9 := (fun mask => (mask,id))

def c37366 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37366 : Upper (D 6) (R 6) [34,129,264,18,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,18,96] 13 (by decide) (choices 1) [1,4,64] r37366 c37366
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22545
  · exact u22546
  · exact u22547

def b37367 : PairBound 9 := { available := 100, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 28 19 100 100 228 356), lower := (rows 35 131 268 28 19 32 64 128 256), losses := [] }

theorem u37367 : Upper (D 6) (R 6) [34,129,264,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37367 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37368 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 268 28 21 98 98 226 354), lower := (rows 35 131 268 28 21 32 64 128 256), losses := [] }

theorem u37368 : Upper (D 6) (R 6) [34,129,264,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37368 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37369 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 268 28 22 97 97 225 353), lower := (rows 35 131 268 28 22 32 64 128 256), losses := [] }

theorem u37369 : Upper (D 6) (R 6) [34,129,264,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37369 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37370 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 268 28 49 102 70 198 326), lower := (rows 35 131 268 28 49 32 64 128 256), losses := [] }

theorem u37370 : Upper (D 6) (R 6) [34,129,264,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37370 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37371 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 268 28 50 101 69 197 325), lower := (rows 35 131 268 28 50 32 64 128 256), losses := [] }

theorem u37371 : Upper (D 6) (R 6) [34,129,264,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37371 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37372 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 268 28 52 99 67 195 323), lower := (rows 35 131 268 28 52 32 64 128 256), losses := [] }

theorem u37372 : Upper (D 6) (R 6) [34,129,264,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37372 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37373 : Route 9 := (fun mask => (mask,id))

def c37373 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37373 : Upper (D 6) (R 6) [34,129,264,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20,65] 13 (by decide) (choices 1) [2,4,64] r37373 c37373
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22548
  · exact u22549
  · exact u22550

def r37374 : Route 9 := (fun mask => (mask,id))

def c37374 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37374 : Upper (D 6) (R 6) [34,129,264,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20,66] 13 (by decide) (choices 1) [1,4,64] r37374 c37374
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22551
  · exact u22552
  · exact u22553

def b37375 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 268 28 84 99 99 227 355), lower := (rows 35 131 268 28 84 32 64 128 256), losses := [] }

theorem u37375 : Upper (D 6) (R 6) [34,129,264,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37375 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37376 : Route 9 := (fun mask => (mask,id))

def c37376 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37376 : Upper (D 6) (R 6) [34,129,264,20,96] 13 := by
  apply FastRouting.sound _ _ [34,129,264,20,96] 13 (by decide) (choices 1) [1,2,4,64] r37376 c37376
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22554
  · exact u22555
  · exact u22556
  · exact u22557

def b37377 : PairBound 9 := { available := 84, camps := [{ cop := 4, region := 364, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 35 131 268 44 19 116 84 212 340), lower := (rows 35 131 268 44 19 32 64 128 256), losses := [] }

theorem u37377 : Upper (D 6) (R 6) [34,129,264,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37377 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37378 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 227, targets := 4 },{ cop := 4, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 35 131 268 44 21 114 82 210 338), lower := (rows 35 131 268 44 21 32 64 128 256), losses := [] }

theorem u37378 : Upper (D 6) (R 6) [34,129,264,36,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37378 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37379 : Route 9 := (fun mask => (mask,id))

def c37379 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37379 : Upper (D 6) (R 6) [34,129,264,36,6] 13 := by
  apply FastRouting.sound _ _ [34,129,264,36,6] 13 (by decide) (choices 1) [1,16,64] r37379 c37379
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22558
  · exact u22559
  · exact u22560

#print axioms u37379
end Delivery.IrregularNine14.P06
