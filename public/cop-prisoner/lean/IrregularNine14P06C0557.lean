import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0274
import IrregularNine14P06C0275
import IrregularNine14P06C0276

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b33420 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 112, targets := 6 },{ cop := 4, region := 454, targets := 32 }], pairs := [(1,5),(4,1),(4,2)], upper := (rows 11 134 262 44 49 113 81 209 337), lower := (rows 11 134 262 44 49 32 64 128 256), losses := [] }

theorem u33420 : Upper (D 6) (R 6) [10,132,258,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33420 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33421 : Route 9 := (fun mask => (mask,id))

def c33421 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33421 : Upper (D 6) (R 6) [10,132,258,36,65] 13 := by
  apply FastRouting.sound _ _ [10,132,258,36,65] 13 (by decide) (choices 1) [1,16,64] r33421 c33421
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16482
  · exact u16483
  · exact u16484

def r33422 : Route 9 := (fun mask => (mask,id))

def c33422 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33422 : Upper (D 6) (R 6) [10,132,258,36,96] 13 := by
  apply FastRouting.sound _ _ [10,132,258,36,96] 13 (by decide) (choices 1) [1,16,64] r33422 c33422
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16485
  · exact u16486
  · exact u16487

def r33423 : Route 9 := (fun mask => (mask,id))

def c33423 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33423 : Upper (D 6) (R 6) [10,132,258,48,5] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,5] 13 (by decide) (choices 1) [1,64] r33423 c33423
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16488
  · exact u16489

def b33424 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 262 56 49 101 69 197 325), lower := (rows 11 134 262 56 49 32 64 128 256), losses := [] }

theorem u33424 : Upper (D 6) (R 6) [10,132,258,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33424 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33425 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 262 56 52 97 65 193 321), lower := (rows 11 134 262 56 52 32 64 128 256), losses := [] }

theorem u33425 : Upper (D 6) (R 6) [10,132,258,48,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33425 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33426 : Route 9 := (fun mask => (mask,id))

def c33426 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33426 : Upper (D 6) (R 6) [10,132,258,48,65] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,65] 13 (by decide) (choices 1) [1,4,64] r33426 c33426
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16490
  · exact u16491
  · exact u16492

def r33427 : Route 9 := (fun mask => (mask,id))

def c33427 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33427 : Upper (D 6) (R 6) [10,132,258,48,68] 13 := by
  apply FastRouting.sound _ _ [10,132,258,48,68] 13 (by decide) (choices 1) [1,64] r33427 c33427
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16493
  · exact u16494

def b33428 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 134 262 56 112 101 69 197 325), lower := (rows 11 134 262 56 112 32 64 128 256), losses := [] }

theorem u33428 : Upper (D 6) (R 6) [10,132,258,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33428 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33429 : Route 9 := (fun mask => (mask,id))

def c33429 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33429 : Upper (D 6) (R 6) [10,132,258,96,5] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96,5] 13 (by decide) (choices 1) [1,16,64] r33429 c33429
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16495
  · exact u16496
  · exact u16497

def r33430 : Route 9 := (fun mask => (mask,id))

def c33430 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33430 : Upper (D 6) (R 6) [10,132,258,96,33] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96,33] 13 (by decide) (choices 1) [1,4,16,64] r33430 c33430
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16498
  · exact u16499
  · exact u16500
  · exact u16501

def r33431 : Route 9 := (fun mask => (mask,id))

def c33431 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33431 : Upper (D 6) (R 6) [10,132,258,96,36] 13 := by
  apply FastRouting.sound _ _ [10,132,258,96,36] 13 (by decide) (choices 1) [1,16,64] r33431 c33431
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16502
  · exact u16503
  · exact u16504

def b33432 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 134 262 104 112 53 85 149 277), lower := (rows 11 134 262 104 112 32 64 128 256), losses := [] }

theorem u33432 : Upper (D 6) (R 6) [10,132,258,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33432 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33433 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 276 41 19 100 100 228 356), lower := (rows 11 134 276 41 19 32 64 128 256), losses := [] }

theorem u33433 : Upper (D 6) (R 6) [10,132,272,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33433 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33434 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 105, targets := 4 },{ cop := 4, region := 226, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 134 276 41 21 98 98 226 354), lower := (rows 11 134 276 41 21 32 64 128 256), losses := [] }

theorem u33434 : Upper (D 6) (R 6) [10,132,272,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33434 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33435 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 276 41 22 97 97 225 353), lower := (rows 11 134 276 41 22 32 64 128 256), losses := [] }

theorem u33435 : Upper (D 6) (R 6) [10,132,272,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33435 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33436 : PairBound 9 := { available := 70, camps := [{ cop := 3, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 11 134 276 41 49 102 70 198 326), lower := (rows 11 134 276 41 49 32 64 128 256), losses := [] }

theorem u33436 : Upper (D 6) (R 6) [10,132,272,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33436 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33437 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 68 }], pairs := [(0,2),(0,6),(3,2)], upper := (rows 11 134 276 41 50 101 69 197 325), lower := (rows 11 134 276 41 50 32 64 128 256), losses := [] }

theorem u33437 : Upper (D 6) (R 6) [10,132,272,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33437 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33438 : Route 9 := (fun mask => (mask,id))

def c33438 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33438 : Upper (D 6) (R 6) [10,132,272,33,36] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,36] 13 (by decide) (choices 1) [1,2,64] r33438 c33438
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16505
  · exact u16506
  · exact u16507

def r33439 : Route 9 := (fun mask => (mask,id))

def c33439 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33439 : Upper (D 6) (R 6) [10,132,272,33,65] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,65] 13 (by decide) (choices 1) [2,4,64] r33439 c33439
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16508
  · exact u16509
  · exact u16510

def r33440 : Route 9 := (fun mask => (mask,id))

def c33440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33440 : Upper (D 6) (R 6) [10,132,272,33,66] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,66] 13 (by decide) (choices 1) [1,4,64] r33440 c33440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16511
  · exact u16512
  · exact u16513

def r33441 : Route 9 := (fun mask => (mask,id))

def c33441 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33441 : Upper (D 6) (R 6) [10,132,272,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,68] 13 (by decide) (choices 1) [1,2,64] r33441 c33441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16514
  · exact u16515
  · exact u16516

def r33442 : Route 9 := (fun mask => (mask,id))

def c33442 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33442 : Upper (D 6) (R 6) [10,132,272,33,96] 13 := by
  apply FastRouting.sound _ _ [10,132,272,33,96] 13 (by decide) (choices 1) [1,2,4,64] r33442 c33442
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16517
  · exact u16518
  · exact u16519
  · exact u16520

def b33443 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 16, targets := 96 },{ cop := 4, region := 356, targets := 2 }], pairs := [(2,1),(4,5),(4,6)], upper := (rows 11 134 276 44 19 97 97 225 353), lower := (rows 11 134 276 44 19 32 64 128 256), losses := [] }

theorem u33443 : Upper (D 6) (R 6) [10,132,272,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33443 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33444 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 276 44 49 99 67 195 323), lower := (rows 11 134 276 44 49 32 64 128 256), losses := [] }

theorem u33444 : Upper (D 6) (R 6) [10,132,272,36,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33445 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 276 44 50 97 65 193 321), lower := (rows 11 134 276 44 50 32 64 128 256), losses := [] }

theorem u33445 : Upper (D 6) (R 6) [10,132,272,36,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33446 : Route 9 := (fun mask => (mask,id))

def c33446 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33446 : Upper (D 6) (R 6) [10,132,272,36,65] 13 := by
  apply FastRouting.sound _ _ [10,132,272,36,65] 13 (by decide) (choices 1) [1,2,64] r33446 c33446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16521
  · exact u16522
  · exact u16523

def r33447 : Route 9 := (fun mask => (mask,id))

def c33447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33447 : Upper (D 6) (R 6) [10,132,272,36,66] 13 := by
  apply FastRouting.sound _ _ [10,132,272,36,66] 13 (by decide) (choices 1) [1,64] r33447 c33447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16524
  · exact u16525

def b33448 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 276 44 112 99 67 195 323), lower := (rows 11 134 276 44 112 32 64 128 256), losses := [] }

theorem u33448 : Upper (D 6) (R 6) [10,132,272,36,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33448 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33449 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 276 104 19 101 101 229 357), lower := (rows 11 134 276 104 19 32 64 128 256), losses := [] }

theorem u33449 : Upper (D 6) (R 6) [10,132,272,96,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33449 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33450 : Route 9 := (fun mask => (mask,id))

def c33450 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33450 : Upper (D 6) (R 6) [10,132,272,96,5] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,5] 13 (by decide) (choices 1) [1,2,64] r33450 c33450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16526
  · exact u16527
  · exact u16528

def b33451 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 276 104 22 97 97 225 353), lower := (rows 11 134 276 104 22 32 64 128 256), losses := [] }

theorem u33451 : Upper (D 6) (R 6) [10,132,272,96,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33451 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33452 : Route 9 := (fun mask => (mask,id))

def c33452 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33452 : Upper (D 6) (R 6) [10,132,272,96,33] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,33] 13 (by decide) (choices 1) [1,2,4,64] r33452 c33452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16529
  · exact u16530
  · exact u16531
  · exact u16532

def r33453 : Route 9 := (fun mask => (mask,id))

def c33453 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33453 : Upper (D 6) (R 6) [10,132,272,96,34] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,34] 13 (by decide) (choices 1) [1,4,64] r33453 c33453
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16533
  · exact u16534
  · exact u16535

def r33454 : Route 9 := (fun mask => (mask,id))

def c33454 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33454 : Upper (D 6) (R 6) [10,132,272,96,36] 13 := by
  apply FastRouting.sound _ _ [10,132,272,96,36] 13 (by decide) (choices 1) [1,2,64] r33454 c33454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16536
  · exact u16537
  · exact u16538

def b33455 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 134 276 104 112 39 71 135 263), lower := (rows 11 134 276 104 112 32 64 128 256), losses := [] }

theorem u33455 : Upper (D 6) (R 6) [10,132,272,96,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33455 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33456 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 25, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 25 19 100 100 228 356), lower := (rows 11 134 292 25 19 32 64 128 256), losses := [] }

theorem u33456 : Upper (D 6) (R 6) [10,132,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33456 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33457 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 292 25 21 98 98 226 354), lower := (rows 11 134 292 25 21 32 64 128 256), losses := [] }

theorem u33457 : Upper (D 6) (R 6) [10,132,288,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33458 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 292 25 22 97 97 225 353), lower := (rows 11 134 292 25 22 32 64 128 256), losses := [] }

theorem u33458 : Upper (D 6) (R 6) [10,132,288,17,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33458 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33459 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 292 25 49 102 70 198 326), lower := (rows 11 134 292 25 49 32 64 128 256), losses := [] }

theorem u33459 : Upper (D 6) (R 6) [10,132,288,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33460 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 25 50 101 69 197 325), lower := (rows 11 134 292 25 50 32 64 128 256), losses := [] }

theorem u33460 : Upper (D 6) (R 6) [10,132,288,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33461 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 16, targets := 67 }], pairs := [(4,0),(4,1),(4,6)], upper := (rows 11 134 292 25 52 99 67 195 323), lower := (rows 11 134 292 25 52 32 64 128 256), losses := [] }

theorem u33461 : Upper (D 6) (R 6) [10,132,288,17,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33462 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 11 134 292 25 81 102 102 230 358), lower := (rows 11 134 292 25 81 32 64 128 256), losses := [] }

theorem u33462 : Upper (D 6) (R 6) [10,132,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33463 : PairBound 9 := { available := 101, camps := [{ cop := 4, region := 9, targets := 100 }], pairs := [(0,2),(0,5),(0,6)], upper := (rows 11 134 292 25 82 101 101 229 357), lower := (rows 11 134 292 25 82 32 64 128 256), losses := [] }

theorem u33463 : Upper (D 6) (R 6) [10,132,288,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33464 : Route 9 := (fun mask => (mask,id))

def c33464 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33464 : Upper (D 6) (R 6) [10,132,288,17,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,68] 13 (by decide) (choices 1) [1,2,64] r33464 c33464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16539
  · exact u16540
  · exact u16541

def r33465 : Route 9 := (fun mask => (mask,id))

def c33465 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33465 : Upper (D 6) (R 6) [10,132,288,17,96] 13 := by
  apply FastRouting.sound _ _ [10,132,288,17,96] 13 (by decide) (choices 1) [1,2,4,64] r33465 c33465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16542
  · exact u16543
  · exact u16544
  · exact u16545

def b33466 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 25, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 134 292 28 19 97 97 225 353), lower := (rows 11 134 292 28 19 32 64 128 256), losses := [] }

theorem u33466 : Upper (D 6) (R 6) [10,132,288,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33467 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 292 28 49 99 67 195 323), lower := (rows 11 134 292 28 49 32 64 128 256), losses := [] }

theorem u33467 : Upper (D 6) (R 6) [10,132,288,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33468 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 356, targets := 2 }], pairs := [(0,5),(1,5),(2,1)], upper := (rows 11 134 292 28 50 97 65 193 321), lower := (rows 11 134 292 28 50 32 64 128 256), losses := [] }

theorem u33468 : Upper (D 6) (R 6) [10,132,288,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33469 : Route 9 := (fun mask => (mask,id))

def c33469 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33469 : Upper (D 6) (R 6) [10,132,288,20,65] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,65] 13 (by decide) (choices 1) [1,2,64] r33469 c33469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u16546
  · exact u16547
  · exact u16548

def r33470 : Route 9 := (fun mask => (mask,id))

def c33470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33470 : Upper (D 6) (R 6) [10,132,288,20,66] 13 := by
  apply FastRouting.sound _ _ [10,132,288,20,66] 13 (by decide) (choices 1) [1,64] r33470 c33470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u16549
  · exact u16550

def b33471 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 195, targets := 32 },{ cop := 0, region := 112, targets := 4 }], pairs := [(0,5),(1,5),(4,2)], upper := (rows 11 134 292 28 112 99 67 195 323), lower := (rows 11 134 292 28 112 32 64 128 256), losses := [] }

theorem u33471 : Upper (D 6) (R 6) [10,132,288,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33472 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 292 41 19 116 84 212 340), lower := (rows 11 134 292 41 19 32 64 128 256), losses := [] }

theorem u33472 : Upper (D 6) (R 6) [10,132,288,33,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33472 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33473 : PairBound 9 := { available := 82, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 194, targets := 32 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 11 134 292 41 21 114 82 210 338), lower := (rows 11 134 292 41 21 32 64 128 256), losses := [] }

theorem u33473 : Upper (D 6) (R 6) [10,132,288,33,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33473 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33474 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 11 134 292 41 22 113 81 209 337), lower := (rows 11 134 292 41 22 32 64 128 256), losses := [] }

theorem u33474 : Upper (D 6) (R 6) [10,132,288,33,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r33475 : Route 9 := (fun mask => (mask,id))

def c33475 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33475 : Upper (D 6) (R 6) [10,132,288,33,65] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,65] 13 (by decide) (choices 1) [2,4,16,64] r33475 c33475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16551
  · exact u16552
  · exact u16553
  · exact u16554

def r33476 : Route 9 := (fun mask => (mask,id))

def c33476 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33476 : Upper (D 6) (R 6) [10,132,288,33,66] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,66] 13 (by decide) (choices 1) [1,4,16,64] r33476 c33476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16555
  · exact u16556
  · exact u16557
  · exact u16558

def r33477 : Route 9 := (fun mask => (mask,id))

def c33477 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u33477 : Upper (D 6) (R 6) [10,132,288,33,68] 13 := by
  apply FastRouting.sound _ _ [10,132,288,33,68] 13 (by decide) (choices 1) [1,2,16,64] r33477 c33477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u16559
  · exact u16560
  · exact u16561
  · exact u16562

def b33478 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 134 292 56 19 101 69 197 325), lower := (rows 11 134 292 56 19 32 64 128 256), losses := [] }

theorem u33478 : Upper (D 6) (R 6) [10,132,288,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33478 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b33479 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 194, targets := 32 }], pairs := [(0,5),(1,5),(3,2)], upper := (rows 11 134 292 56 21 99 67 195 323), lower := (rows 11 134 292 56 21 32 64 128 256), losses := [{ target := 2, region := (rows 1 2 0 24 16 33 65 129 257), good := (rows 491 130 288 56 505 32 64 128 256) },{ target := 5, region := (rows 9 18 4 8 16 0 89 153 281), good := (rows 459 134 260 475 471 0 64 128 256) }] }

theorem u33479 : Upper (D 6) (R 6) [10,132,288,48,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b33479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u33479
end Delivery.IrregularNine14.P06
