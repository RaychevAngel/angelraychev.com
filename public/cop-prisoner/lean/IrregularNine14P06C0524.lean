import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0226
import IrregularNine14P06C0227
import IrregularNine14P06C0228

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r31440 : Route 9 := (fun mask => (mask,id))

def c31440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31440 : Upper (D 6) (R 6) [10,36,130,48,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,260] 13 (by decide) (choices 1) [1,64] r31440 c31440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13567
  · exact u13568

def r31441 : Route 9 := (fun mask => (mask,id))

def c31441 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31441 : Upper (D 6) (R 6) [10,36,130,48,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,48,320] 13 (by decide) (choices 1) [1,4,64] r31441 c31441
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13569
  · exact u13570
  · exact u13571

def b31442 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 486, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 73 21 368 368 496 368), lower := (rows 11 38 134 73 21 32 64 128 256), losses := [] }

theorem u31442 : Upper (D 6) (R 6) [10,36,130,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31443 : Route 9 := (fun mask => (mask,id))

def c31443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31443 : Upper (D 6) (R 6) [10,36,130,65,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,33] 13 (by decide) (choices 1) [4,16,64,256] r31443 c31443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13572
  · exact u13573
  · exact u13574
  · exact u13575

def b31444 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 134 73 52 369 337 465 337), lower := (rows 11 38 134 73 52 32 64 128 256), losses := [] }

theorem u31444 : Upper (D 6) (R 6) [10,36,130,65,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31444 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31445 : PairBound 9 := { available := 308, camps := [{ cop := 3, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 11 38 134 73 81 308 372 436 308), lower := (rows 11 38 134 73 81 32 64 128 256), losses := [] }

theorem u31445 : Upper (D 6) (R 6) [10,36,130,65,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31445 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31446 : Route 9 := (fun mask => (mask,id))

def c31446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31446 : Upper (D 6) (R 6) [10,36,130,65,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,68] 13 (by decide) (choices 1) [1,16,256] r31446 c31446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13576
  · exact u13577
  · exact u13578

def r31447 : Route 9 := (fun mask => (mask,id))

def c31447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31447 : Upper (D 6) (R 6) [10,36,130,65,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,96] 13 (by decide) (choices 1) [1,4,16,256] r31447 c31447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13579
  · exact u13580
  · exact u13581
  · exact u13582

def r31448 : Route 9 := (fun mask => (mask,id))

def c31448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31448 : Upper (D 6) (R 6) [10,36,130,65,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,257] 13 (by decide) (choices 1) [4,16,64] r31448 c31448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13583
  · exact u13584
  · exact u13585

def r31449 : Route 9 := (fun mask => (mask,id))

def c31449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31449 : Upper (D 6) (R 6) [10,36,130,65,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,260] 13 (by decide) (choices 1) [1,16,64] r31449 c31449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13586
  · exact u13587
  · exact u13588

def r31450 : Route 9 := (fun mask => (mask,id))

def c31450 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31450 : Upper (D 6) (R 6) [10,36,130,65,288] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,288] 13 (by decide) (choices 1) [1,4,16,64] r31450 c31450
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13589
  · exact u13590
  · exact u13591
  · exact u13592

def r31451 : Route 9 := (fun mask => (mask,id))

def c31451 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31451 : Upper (D 6) (R 6) [10,36,130,65,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,65,320] 13 (by decide) (choices 1) [1,4,16] r31451 c31451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13593
  · exact u13594
  · exact u13595

def r31452 : Route 9 := (fun mask => (mask,id))

def c31452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u31452 : Upper (D 6) (R 6) [10,36,130,68,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68,33] 13 (by decide) (choices 1) [1,16,64,256] r31452 c31452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13596
  · exact u13597
  · exact u13598
  · exact u13599

def b31453 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 368, targets := 6 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(4,1),(4,2)], upper := (rows 11 38 134 76 81 305 369 433 305), lower := (rows 11 38 134 76 81 32 64 128 256), losses := [] }

theorem u31453 : Upper (D 6) (R 6) [10,36,130,68,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31454 : Route 9 := (fun mask => (mask,id))

def c31454 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31454 : Upper (D 6) (R 6) [10,36,130,68,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68,96] 13 (by decide) (choices 1) [1,16,256] r31454 c31454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13600
  · exact u13601
  · exact u13602

def r31455 : Route 9 := (fun mask => (mask,id))

def c31455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31455 : Upper (D 6) (R 6) [10,36,130,68,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68,257] 13 (by decide) (choices 1) [1,16,64] r31455 c31455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13603
  · exact u13604
  · exact u13605

def r31456 : Route 9 := (fun mask => (mask,id))

def c31456 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31456 : Upper (D 6) (R 6) [10,36,130,68,288] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68,288] 13 (by decide) (choices 1) [1,16,64] r31456 c31456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13606
  · exact u13607
  · exact u13608

def r31457 : Route 9 := (fun mask => (mask,id))

def c31457 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31457 : Upper (D 6) (R 6) [10,36,130,68,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,68,320] 13 (by decide) (choices 1) [1,16] r31457 c31457
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13609
  · exact u13610

def r31458 : Route 9 := (fun mask => (mask,id))

def c31458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31458 : Upper (D 6) (R 6) [10,36,130,80,5] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,5] 13 (by decide) (choices 1) [1,64,256] r31458 c31458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13611
  · exact u13612
  · exact u13613

def r31459 : Route 9 := (fun mask => (mask,id))

def c31459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u31459 : Upper (D 6) (R 6) [10,36,130,80,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,33] 13 (by decide) (choices 1) [1,4,64,256] r31459 c31459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13614
  · exact u13615
  · exact u13616
  · exact u13617

def b31460 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 134 88 52 353 321 449 321), lower := (rows 11 38 134 88 52 32 64 128 256), losses := [] }

theorem u31460 : Upper (D 6) (R 6) [10,36,130,80,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31461 : PairBound 9 := { available := 293, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 134 88 81 293 357 421 293), lower := (rows 11 38 134 88 81 32 64 128 256), losses := [] }

theorem u31461 : Upper (D 6) (R 6) [10,36,130,80,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31462 : PairBound 9 := { available := 289, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 134 88 84 289 353 417 289), lower := (rows 11 38 134 88 84 32 64 128 256), losses := [] }

theorem u31462 : Upper (D 6) (R 6) [10,36,130,80,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31463 : PairBound 9 := { available := 261, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 134 88 112 293 325 389 261), lower := (rows 11 38 134 88 112 32 64 128 256), losses := [] }

theorem u31463 : Upper (D 6) (R 6) [10,36,130,80,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31464 : Route 9 := (fun mask => (mask,id))

def c31464 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31464 : Upper (D 6) (R 6) [10,36,130,80,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,257] 13 (by decide) (choices 1) [1,4,64] r31464 c31464
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13618
  · exact u13619
  · exact u13620

def r31465 : Route 9 := (fun mask => (mask,id))

def c31465 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31465 : Upper (D 6) (R 6) [10,36,130,80,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,260] 13 (by decide) (choices 1) [1,64] r31465 c31465
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13621
  · exact u13622

def r31466 : Route 9 := (fun mask => (mask,id))

def c31466 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31466 : Upper (D 6) (R 6) [10,36,130,80,288] 13 := by
  apply FastRouting.sound _ _ [10,36,130,80,288] 13 (by decide) (choices 1) [1,4,64] r31466 c31466
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13623
  · exact u13624
  · exact u13625

def b31467 : PairBound 9 := { available := 37, camps := [{ cop := 4, region := 8, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 38 134 88 336 37 101 165 293), lower := (rows 11 38 134 88 336 32 64 128 256), losses := [] }

theorem u31467 : Upper (D 6) (R 6) [10,36,130,80,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31468 : PairBound 9 := { available := 337, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 104 21 369 337 465 337), lower := (rows 11 38 134 104 21 32 64 128 256), losses := [] }

theorem u31468 : Upper (D 6) (R 6) [10,36,130,96,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31468 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31469 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 468, targets := 32 },{ cop := 4, region := 422, targets := 64 }], pairs := [(1,6),(2,5),(4,5)], upper := (rows 11 38 134 104 81 309 341 405 277), lower := (rows 11 38 134 104 81 32 64 128 256), losses := [] }

theorem u31469 : Upper (D 6) (R 6) [10,36,130,96,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31469 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31470 : Route 9 := (fun mask => (mask,id))

def c31470 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u31470 : Upper (D 6) (R 6) [10,36,130,96,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,68] 13 (by decide) (choices 1) [1,16,256] r31470 c31470
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13626
  · exact u13627
  · exact u13628

def r31471 : Route 9 := (fun mask => (mask,id))

def c31471 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31471 : Upper (D 6) (R 6) [10,36,130,96,257] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,257] 13 (by decide) (choices 1) [1,4,16,64] r31471 c31471
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13629
  · exact u13630
  · exact u13631
  · exact u13632

def r31472 : Route 9 := (fun mask => (mask,id))

def c31472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31472 : Upper (D 6) (R 6) [10,36,130,96,260] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,260] 13 (by decide) (choices 1) [1,16,64] r31472 c31472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13633
  · exact u13634
  · exact u13635

def r31473 : Route 9 := (fun mask => (mask,id))

def c31473 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31473 : Upper (D 6) (R 6) [10,36,130,96,320] 13 := by
  apply FastRouting.sound _ _ [10,36,130,96,320] 13 (by decide) (choices 1) [1,4,16] r31473 c31473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13636
  · exact u13637
  · exact u13638

def b31474 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 230, targets := 1 },{ cop := 4, region := 360, targets := 2 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 38 134 265 21 112 112 240 368), lower := (rows 11 38 134 265 21 32 64 128 256), losses := [] }

theorem u31474 : Upper (D 6) (R 6) [10,36,130,257,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31474 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31475 : Route 9 := (fun mask => (mask,id))

def c31475 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31475 : Upper (D 6) (R 6) [10,36,130,257,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,33] 13 (by decide) (choices 1) [4,16,64] r31475 c31475
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13639
  · exact u13640
  · exact u13641

def b31476 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 134 265 52 113 81 209 337), lower := (rows 11 38 134 265 52 32 64 128 256), losses := [] }

theorem u31476 : Upper (D 6) (R 6) [10,36,130,257,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31476 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31477 : Route 9 := (fun mask => (mask,id))

def c31477 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31477 : Upper (D 6) (R 6) [10,36,130,257,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,65] 13 (by decide) (choices 1) [4,16,64] r31477 c31477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13642
  · exact u13643
  · exact u13644

def r31478 : Route 9 := (fun mask => (mask,id))

def c31478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31478 : Upper (D 6) (R 6) [10,36,130,257,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,68] 13 (by decide) (choices 1) [1,16,64] r31478 c31478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13645
  · exact u13646
  · exact u13647

def r31479 : Route 9 := (fun mask => (mask,id))

def c31479 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31479 : Upper (D 6) (R 6) [10,36,130,257,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,257,96] 13 (by decide) (choices 1) [1,4,16,64] r31479 c31479
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13648
  · exact u13649
  · exact u13650
  · exact u13651

def r31480 : Route 9 := (fun mask => (mask,id))

def c31480 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31480 : Upper (D 6) (R 6) [10,36,130,260,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260,33] 13 (by decide) (choices 1) [1,16,64] r31480 c31480
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13652
  · exact u13653
  · exact u13654

def r31481 : Route 9 := (fun mask => (mask,id))

def c31481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31481 : Upper (D 6) (R 6) [10,36,130,260,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260,65] 13 (by decide) (choices 1) [1,16,64] r31481 c31481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13655
  · exact u13656
  · exact u13657

def r31482 : Route 9 := (fun mask => (mask,id))

def c31482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31482 : Upper (D 6) (R 6) [10,36,130,260,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,260,96] 13 (by decide) (choices 1) [1,16,64] r31482 c31482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13658
  · exact u13659
  · exact u13660

def r31483 : Route 9 := (fun mask => (mask,id))

def c31483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31483 : Upper (D 6) (R 6) [10,36,130,272,5] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,5] 13 (by decide) (choices 1) [1,64] r31483 c31483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13661
  · exact u13662

def r31484 : Route 9 := (fun mask => (mask,id))

def c31484 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31484 : Upper (D 6) (R 6) [10,36,130,272,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,33] 13 (by decide) (choices 1) [1,4,64] r31484 c31484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13663
  · exact u13664
  · exact u13665

def b31485 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 134 280 52 97 65 193 321), lower := (rows 11 38 134 280 52 32 64 128 256), losses := [] }

theorem u31485 : Upper (D 6) (R 6) [10,36,130,272,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31485 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31486 : Route 9 := (fun mask => (mask,id))

def c31486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31486 : Upper (D 6) (R 6) [10,36,130,272,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,65] 13 (by decide) (choices 1) [1,4,64] r31486 c31486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13666
  · exact u13667
  · exact u13668

def r31487 : Route 9 := (fun mask => (mask,id))

def c31487 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31487 : Upper (D 6) (R 6) [10,36,130,272,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,68] 13 (by decide) (choices 1) [1,64] r31487 c31487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13669
  · exact u13670

def r31488 : Route 9 := (fun mask => (mask,id))

def c31488 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31488 : Upper (D 6) (R 6) [10,36,130,272,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,272,96] 13 (by decide) (choices 1) [1,4,64] r31488 c31488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13671
  · exact u13672
  · exact u13673

def b31489 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 212, targets := 32 },{ cop := 4, region := 360, targets := 2 }], pairs := [(2,5),(3,1),(4,5)], upper := (rows 11 38 134 296 21 113 81 209 337), lower := (rows 11 38 134 296 21 32 64 128 256), losses := [] }

theorem u31489 : Upper (D 6) (R 6) [10,36,130,288,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31490 : Route 9 := (fun mask => (mask,id))

def c31490 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31490 : Upper (D 6) (R 6) [10,36,130,288,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288,65] 13 (by decide) (choices 1) [1,4,16,64] r31490 c31490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13674
  · exact u13675
  · exact u13676
  · exact u13677

def r31491 : Route 9 := (fun mask => (mask,id))

def c31491 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31491 : Upper (D 6) (R 6) [10,36,130,288,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,288,68] 13 (by decide) (choices 1) [1,16,64] r31491 c31491
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13678
  · exact u13679
  · exact u13680

def r31492 : Route 9 := (fun mask => (mask,id))

def c31492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31492 : Upper (D 6) (R 6) [10,36,130,320,5] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,5] 13 (by decide) (choices 1) [1,16,64] r31492 c31492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13681
  · exact u13682
  · exact u13683

def r31493 : Route 9 := (fun mask => (mask,id))

def c31493 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31493 : Upper (D 6) (R 6) [10,36,130,320,33] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,33] 13 (by decide) (choices 1) [1,4,16,64] r31493 c31493
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u13684
  · exact u13685
  · exact u13686
  · exact u13687

def b31494 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 16, targets := 65 },{ cop := 4, region := 2, targets := 1 }], pairs := [(1,0),(4,0),(4,6)], upper := (rows 11 38 134 328 52 113 81 209 337), lower := (rows 11 38 134 328 52 32 64 128 256), losses := [] }

theorem u31494 : Upper (D 6) (R 6) [10,36,130,320,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r31495 : Route 9 := (fun mask => (mask,id))

def c31495 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31495 : Upper (D 6) (R 6) [10,36,130,320,65] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,65] 13 (by decide) (choices 1) [1,4,16] r31495 c31495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13688
  · exact u13689
  · exact u13690

def r31496 : Route 9 := (fun mask => (mask,id))

def c31496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31496 : Upper (D 6) (R 6) [10,36,130,320,68] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,68] 13 (by decide) (choices 1) [1,16] r31496 c31496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u13691
  · exact u13692

def r31497 : Route 9 := (fun mask => (mask,id))

def c31497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u31497 : Upper (D 6) (R 6) [10,36,130,320,96] 13 := by
  apply FastRouting.sound _ _ [10,36,130,320,96] 13 (by decide) (choices 1) [1,4,16] r31497 c31497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u13693
  · exact u13694
  · exact u13695

def b31498 : PairBound 9 := { available := 356, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 11 38 148 73 19 356 356 484 356), lower := (rows 11 38 148 73 19 32 64 128 256), losses := [] }

theorem u31498 : Upper (D 6) (R 6) [10,36,144,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31498 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b31499 : PairBound 9 := { available := 354, camps := [{ cop := 1, region := 329, targets := 4 },{ cop := 4, region := 354, targets := 1 }], pairs := [(0,2),(1,0),(3,2)], upper := (rows 11 38 148 73 21 354 354 482 354), lower := (rows 11 38 148 73 21 32 64 128 256), losses := [] }

theorem u31499 : Upper (D 6) (R 6) [10,36,144,65,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b31499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u31499
end Delivery.IrregularNine14.P06
