import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0458
import IrregularNine14P07C0459
import IrregularNine14P07C0460

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b39480 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 76 11 49 178 210 146 402), lower := (rows 37 322 76 11 49 32 64 128 256), losses := [] }

theorem u39480 : Upper (D 7) (R 7) [36,320,72,3,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39480 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39481 : Route 9 := (fun mask => (mask,id))

def c39481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39481 : Upper (D 7) (R 7) [36,320,72,3,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,34] 13 (by decide) (choices 1) [1,16,128] r39481 c39481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27522
  · exact u27523
  · exact u27524

def r39482 : Route 9 := (fun mask => (mask,id))

def c39482 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39482 : Upper (D 7) (R 7) [36,320,72,3,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,129] 13 (by decide) (choices 1) [2,16,128] r39482 c39482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27525
  · exact u27526
  · exact u27527

def r39483 : Route 9 := (fun mask => (mask,id))

def c39483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39483 : Upper (D 7) (R 7) [36,320,72,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,130] 13 (by decide) (choices 1) [1,16,128] r39483 c39483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27528
  · exact u27529
  · exact u27530

def r39484 : Route 9 := (fun mask => (mask,id))

def c39484 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39484 : Upper (D 7) (R 7) [36,320,72,3,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,3,160] 13 (by decide) (choices 1) [1,2,16,128] r39484 c39484
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27531
  · exact u27532
  · exact u27533
  · exact u27534

def b39485 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 162 },{ cop := 3, region := 482, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 37 322 76 25 19 162 226 162 418), lower := (rows 37 322 76 25 19 32 64 128 256), losses := [] }

theorem u39485 : Upper (D 7) (R 7) [36,320,72,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39485 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39486 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 76 25 49 162 194 130 386), lower := (rows 37 322 76 25 49 32 64 128 256), losses := [] }

theorem u39486 : Upper (D 7) (R 7) [36,320,72,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39486 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39487 : Route 9 := (fun mask => (mask,id))

def c39487 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39487 : Upper (D 7) (R 7) [36,320,72,17,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,34] 13 (by decide) (choices 1) [1,2,128] r39487 c39487
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27535
  · exact u27536
  · exact u27537

def b39488 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 8, targets := 226 }], pairs := [(3,1),(3,5),(3,6),(3,7)], upper := (rows 37 322 76 25 145 162 226 162 418), lower := (rows 37 322 76 25 145 32 64 128 256), losses := [] }

theorem u39488 : Upper (D 7) (R 7) [36,320,72,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39488 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39489 : Route 9 := (fun mask => (mask,id))

def c39489 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39489 : Upper (D 7) (R 7) [36,320,72,17,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,130] 13 (by decide) (choices 1) [1,2,128] r39489 c39489
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27538
  · exact u27539
  · exact u27540

def r39490 : Route 9 := (fun mask => (mask,id))

def c39490 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39490 : Upper (D 7) (R 7) [36,320,72,17,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,17,160] 13 (by decide) (choices 1) [1,2,128] r39490 c39490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27541
  · exact u27542
  · exact u27543

def b39491 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 161 },{ cop := 3, region := 229, targets := 2 }], pairs := [(0,1),(3,0),(3,5),(3,7)], upper := (rows 37 322 76 26 19 161 225 161 417), lower := (rows 37 322 76 26 19 32 64 128 256), losses := [] }

theorem u39491 : Upper (D 7) (R 7) [36,320,72,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39491 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39492 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 76 26 49 163 195 131 387), lower := (rows 37 322 76 26 49 32 64 128 256), losses := [] }

theorem u39492 : Upper (D 7) (R 7) [36,320,72,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39492 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39493 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 76 26 50 161 193 129 385), lower := (rows 37 322 76 26 50 32 64 128 256), losses := [] }

theorem u39493 : Upper (D 7) (R 7) [36,320,72,18,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39493 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39494 : Route 9 := (fun mask => (mask,id))

def c39494 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39494 : Upper (D 7) (R 7) [36,320,72,18,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,18,129] 13 (by decide) (choices 1) [1,2,128] r39494 c39494
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27544
  · exact u27545
  · exact u27546

def b39495 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 8, targets := 225 }], pairs := [(3,0),(3,5),(3,6),(3,7)], upper := (rows 37 322 76 26 146 161 225 161 417), lower := (rows 37 322 76 26 146 32 64 128 256), losses := [] }

theorem u39495 : Upper (D 7) (R 7) [36,320,72,18,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39495 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39496 : Route 9 := (fun mask => (mask,id))

def c39496 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39496 : Upper (D 7) (R 7) [36,320,72,18,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,18,160] 13 (by decide) (choices 1) [1,2,128] r39496 c39496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27547
  · exact u27548
  · exact u27549

def r39497 : Route 9 := (fun mask => (mask,id))

def c39497 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39497 : Upper (D 7) (R 7) [36,320,72,34,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,3] 13 (by decide) (choices 1) [1,16,128] r39497 c39497
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27550
  · exact u27551
  · exact u27552

def r39498 : Route 9 := (fun mask => (mask,id))

def c39498 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39498 : Upper (D 7) (R 7) [36,320,72,34,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,129] 13 (by decide) (choices 1) [1,2,16,128] r39498 c39498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27553
  · exact u27554
  · exact u27555
  · exact u27556

def r39499 : Route 9 := (fun mask => (mask,id))

def c39499 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39499 : Upper (D 7) (R 7) [36,320,72,34,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,34,130] 13 (by decide) (choices 1) [1,16,128] r39499 c39499
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27557
  · exact u27558
  · exact u27559

def b39500 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 466, targets := 32 },{ cop := 4, region := 168, targets := 64 }], pairs := [(1,5),(2,5),(3,6),(4,5)], upper := (rows 37 322 76 56 19 163 195 131 387), lower := (rows 37 322 76 56 19 32 64 128 256), losses := [{ target := 5, region := (rows 1 27 12 8 17 0 81 145 273), good := (rows 471 322 78 478 467 0 64 128 256) }] }

theorem u39500 : Upper (D 7) (R 7) [36,320,72,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39500 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39501 : Route 9 := (fun mask => (mask,id))

def c39501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39501 : Upper (D 7) (R 7) [36,320,72,48,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,48,129] 13 (by decide) (choices 1) [1,2,128] r39501 c39501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27560
  · exact u27561
  · exact u27562

def r39502 : Route 9 := (fun mask => (mask,id))

def c39502 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39502 : Upper (D 7) (R 7) [36,320,72,48,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,48,130] 13 (by decide) (choices 1) [1,2,128] r39502 c39502
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27563
  · exact u27564
  · exact u27565

def r39503 : Route 9 := (fun mask => (mask,id))

def c39503 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39503 : Upper (D 7) (R 7) [36,320,72,129,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,3] 13 (by decide) (choices 1) [2,16,128] r39503 c39503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27566
  · exact u27567
  · exact u27568

def b39504 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 76 137 49 178 210 146 402), lower := (rows 37 322 76 137 49 32 64 128 256), losses := [] }

theorem u39504 : Upper (D 7) (R 7) [36,320,72,129,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39504 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39505 : Route 9 := (fun mask => (mask,id))

def c39505 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39505 : Upper (D 7) (R 7) [36,320,72,129,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,34] 13 (by decide) (choices 1) [1,2,16,128] r39505 c39505
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27569
  · exact u27570
  · exact u27571
  · exact u27572

def b39506 : PairBound 9 := { available := 50, camps := [{ cop := 3, region := 16, targets := 98 },{ cop := 4, region := 8, targets := 2 }], pairs := [(3,1),(4,1),(4,5),(4,6)], upper := (rows 37 322 76 137 145 50 114 178 306), lower := (rows 37 322 76 137 145 32 64 128 256), losses := [] }

theorem u39506 : Upper (D 7) (R 7) [36,320,72,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39506 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39507 : Route 9 := (fun mask => (mask,id))

def c39507 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39507 : Upper (D 7) (R 7) [36,320,72,129,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,130] 13 (by decide) (choices 1) [1,2,16] r39507 c39507
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27573
  · exact u27574
  · exact u27575

def r39508 : Route 9 := (fun mask => (mask,id))

def c39508 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39508 : Upper (D 7) (R 7) [36,320,72,129,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,129,160] 13 (by decide) (choices 1) [1,2,16] r39508 c39508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27576
  · exact u27577
  · exact u27578

def r39509 : Route 9 := (fun mask => (mask,id))

def c39509 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39509 : Upper (D 7) (R 7) [36,320,72,130,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,3] 13 (by decide) (choices 1) [1,16,128] r39509 c39509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27579
  · exact u27580
  · exact u27581

def b39510 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 76 138 49 179 211 147 403), lower := (rows 37 322 76 138 49 32 64 128 256), losses := [] }

theorem u39510 : Upper (D 7) (R 7) [36,320,72,130,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39510 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39511 : Route 9 := (fun mask => (mask,id))

def c39511 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39511 : Upper (D 7) (R 7) [36,320,72,130,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,34] 13 (by decide) (choices 1) [1,16,128] r39511 c39511
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27582
  · exact u27583
  · exact u27584

def r39512 : Route 9 := (fun mask => (mask,id))

def c39512 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39512 : Upper (D 7) (R 7) [36,320,72,130,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,129] 13 (by decide) (choices 1) [1,2,16] r39512 c39512
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27585
  · exact u27586
  · exact u27587

def b39513 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 16, targets := 97 },{ cop := 4, region := 8, targets := 1 }], pairs := [(3,0),(4,0),(4,5),(4,6)], upper := (rows 37 322 76 138 146 49 113 177 305), lower := (rows 37 322 76 138 146 32 64 128 256), losses := [] }

theorem u39513 : Upper (D 7) (R 7) [36,320,72,130,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39513 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39514 : Route 9 := (fun mask => (mask,id))

def c39514 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39514 : Upper (D 7) (R 7) [36,320,72,130,160] 13 := by
  apply FastRouting.sound _ _ [36,320,72,130,160] 13 (by decide) (choices 1) [1,2,16] r39514 c39514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27588
  · exact u27589
  · exact u27590

def r39515 : Route 9 := (fun mask => (mask,id))

def c39515 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39515 : Upper (D 7) (R 7) [36,320,72,144,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,144,3] 13 (by decide) (choices 1) [1,2,128] r39515 c39515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27591
  · exact u27592
  · exact u27593

def b39516 : PairBound 9 := { available := 131, camps := [{ cop := 0, region := 16, targets := 194 },{ cop := 4, region := 450, targets := 32 }], pairs := [(1,5),(4,1),(4,6),(4,7)], upper := (rows 37 322 76 152 49 163 195 131 387), lower := (rows 37 322 76 152 49 32 64 128 256), losses := [] }

theorem u39516 : Upper (D 7) (R 7) [36,320,72,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39516 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39517 : Route 9 := (fun mask => (mask,id))

def c39517 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39517 : Upper (D 7) (R 7) [36,320,72,144,34] 13 := by
  apply FastRouting.sound _ _ [36,320,72,144,34] 13 (by decide) (choices 1) [1,2,128] r39517 c39517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27594
  · exact u27595
  · exact u27596

def b39518 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 76 152 145 35 99 163 291), lower := (rows 37 322 76 152 145 32 64 128 256), losses := [] }

theorem u39518 : Upper (D 7) (R 7) [36,320,72,144,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39518 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39519 : PairBound 9 := { available := 35, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 76 152 146 35 99 163 291), lower := (rows 37 322 76 152 146 32 64 128 256), losses := [] }

theorem u39519 : Upper (D 7) (R 7) [36,320,72,144,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39519 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39520 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 99 }], pairs := [(3,0),(3,1),(3,5),(3,6)], upper := (rows 37 322 76 152 176 35 67 131 259), lower := (rows 37 322 76 152 176 32 64 128 256), losses := [] }

theorem u39520 : Upper (D 7) (R 7) [36,320,72,144,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39520 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39521 : Route 9 := (fun mask => (mask,id))

def c39521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39521 : Upper (D 7) (R 7) [36,320,72,160,3] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160,3] 13 (by decide) (choices 1) [1,2,16,128] r39521 c39521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27597
  · exact u27598
  · exact u27599
  · exact u27600

def r39522 : Route 9 := (fun mask => (mask,id))

def c39522 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39522 : Upper (D 7) (R 7) [36,320,72,160,129] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160,129] 13 (by decide) (choices 1) [1,2,16] r39522 c39522
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27601
  · exact u27602
  · exact u27603

def r39523 : Route 9 := (fun mask => (mask,id))

def c39523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39523 : Upper (D 7) (R 7) [36,320,72,160,130] 13 := by
  apply FastRouting.sound _ _ [36,320,72,160,130] 13 (by decide) (choices 1) [1,2,16] r39523 c39523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27604
  · exact u27605
  · exact u27606

def b39524 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 16, targets := 224 },{ cop := 3, region := 498, targets := 1 }], pairs := [(1,0),(4,5),(4,6),(4,7)], upper := (rows 37 322 133 11 26 240 240 240 496), lower := (rows 37 322 133 11 26 32 64 128 256), losses := [] }

theorem u39524 : Upper (D 7) (R 7) [36,320,129,3,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39524 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39525 : Route 9 := (fun mask => (mask,id))

def c39525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 256 => 8 | _ => 0)

theorem u39525 : Upper (D 7) (R 7) [36,320,129,3,34] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,34] 13 (by decide) (choices 1) [8,16,64,128] r39525 c39525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27607
  · exact u27608
  · exact u27609
  · exact u27610

def r39526 : Route 9 := (fun mask => (mask,id))

def c39526 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u39526 : Upper (D 7) (R 7) [36,320,129,3,40] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,40] 13 (by decide) (choices 1) [2,16,64,128] r39526 c39526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27611
  · exact u27612
  · exact u27613
  · exact u27614

def b39527 : PairBound 9 := { available := 184, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 133 11 82 184 248 184 440), lower := (rows 37 322 133 11 82 32 64 128 256), losses := [] }

theorem u39527 : Upper (D 7) (R 7) [36,320,129,3,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39527 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39528 : Route 9 := (fun mask => (mask,id))

def c39528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39528 : Upper (D 7) (R 7) [36,320,129,3,72] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,72] 13 (by decide) (choices 1) [2,16,128] r39528 c39528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27615
  · exact u27616
  · exact u27617

def r39529 : Route 9 := (fun mask => (mask,id))

def c39529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u39529 : Upper (D 7) (R 7) [36,320,129,3,96] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,96] 13 (by decide) (choices 1) [2,8,16,128] r39529 c39529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27618
  · exact u27619
  · exact u27620
  · exact u27621

def r39530 : Route 9 := (fun mask => (mask,id))

def c39530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39530 : Upper (D 7) (R 7) [36,320,129,3,130] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,130] 13 (by decide) (choices 1) [8,16,64] r39530 c39530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27622
  · exact u27623
  · exact u27624

def r39531 : Route 9 := (fun mask => (mask,id))

def c39531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39531 : Upper (D 7) (R 7) [36,320,129,3,136] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,136] 13 (by decide) (choices 1) [2,16,64] r39531 c39531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27625
  · exact u27626
  · exact u27627

def b39532 : PairBound 9 := { available := 90, camps := [{ cop := 4, region := 5, targets := 66 }], pairs := [(0,1),(0,6),(2,1),(2,6)], upper := (rows 37 322 133 11 176 122 90 218 346), lower := (rows 37 322 133 11 176 32 64 128 256), losses := [] }

theorem u39532 : Upper (D 7) (R 7) [36,320,129,3,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39532 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r39533 : Route 9 := (fun mask => (mask,id))

def c39533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u39533 : Upper (D 7) (R 7) [36,320,129,3,192] 13 := by
  apply FastRouting.sound _ _ [36,320,129,3,192] 13 (by decide) (choices 1) [2,8,16] r39533 c39533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27628
  · exact u27629
  · exact u27630

def r39534 : Route 9 := (fun mask => (mask,id))

def c39534 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u39534 : Upper (D 7) (R 7) [36,320,129,17,10] 13 := by
  apply FastRouting.sound _ _ [36,320,129,17,10] 13 (by decide) (choices 1) [2,64,128] r39534 c39534
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27631
  · exact u27632
  · exact u27633

def b39535 : PairBound 9 := { available := 202, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 133 25 50 234 202 202 458), lower := (rows 37 322 133 25 50 32 64 128 256), losses := [] }

theorem u39535 : Upper (D 7) (R 7) [36,320,129,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39535 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39536 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 24, targets := 194 }], pairs := [(3,1),(3,6),(3,7),(4,1)], upper := (rows 37 322 133 25 56 226 194 194 450), lower := (rows 37 322 133 25 56 32 64 128 256), losses := [] }

theorem u39536 : Upper (D 7) (R 7) [36,320,129,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39536 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39537 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 16, targets := 161 },{ cop := 4, region := 173, targets := 64 }], pairs := [(0,6),(4,0),(4,5),(4,7)], upper := (rows 37 322 133 25 82 170 234 170 426), lower := (rows 37 322 133 25 82 32 64 128 256), losses := [] }

theorem u39537 : Upper (D 7) (R 7) [36,320,129,17,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39537 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39538 : PairBound 9 := { available := 162, camps := [{ cop := 1, region := 165, targets := 64 },{ cop := 3, region := 498, targets := 1 }], pairs := [(0,6),(1,0),(2,6),(4,0)], upper := (rows 37 322 133 25 88 162 226 162 418), lower := (rows 37 322 133 25 88 32 64 128 256), losses := [] }

theorem u39538 : Upper (D 7) (R 7) [36,320,129,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39538 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b39539 : PairBound 9 := { available := 138, camps := [{ cop := 3, region := 498, targets := 1 },{ cop := 3, region := 454, targets := 32 }], pairs := [(1,0),(1,5),(2,5),(4,0)], upper := (rows 37 322 133 25 112 170 202 138 394), lower := (rows 37 322 133 25 112 32 64 128 256), losses := [] }

theorem u39539 : Upper (D 7) (R 7) [36,320,129,17,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b39539 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u39539
end Delivery.IrregularNine14.P07
