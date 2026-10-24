import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0458
import IrregularNine14P06C0459
import IrregularNine14P06C0460

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m40500_4 : Upper (D 6) (R 6) [96,136,272,5,3,4] 13 :=
  permutation_upper _ _ _ [96,136,272,5,3,2] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u27535

def r40500 : Route 9 := (fun mask => (mask,id))

def c40500 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40500 : Upper (D 6) (R 6) [96,136,272,5,3] 13 := by
  apply FastRouting.sound _ _ [96,136,272,5,3] 13 (by decide) (choices 1) [2,4,64] r40500 c40500
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27535
  · exact m40500_4
  · exact u27536

def r40501 : Route 9 := (fun mask => (mask,id))

def c40501 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40501 : Upper (D 6) (R 6) [96,136,272,5,6] 13 := by
  apply FastRouting.sound _ _ [96,136,272,5,6] 13 (by decide) (choices 1) [1,2,64] r40501 c40501
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27537
  · exact u27538
  · exact u27539

def b40502 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 138 276 13 49 102 70 198 326), lower := (rows 97 138 276 13 49 32 64 128 256), losses := [] }

theorem u40502 : Upper (D 6) (R 6) [96,136,272,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40502 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40503 : Route 9 := (fun mask => (mask,id))

def c40503 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40503 : Upper (D 6) (R 6) [96,136,272,5,34] 13 := by
  apply FastRouting.sound _ _ [96,136,272,5,34] 13 (by decide) (choices 1) [1,2,4,64] r40503 c40503
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27540
  · exact u27541
  · exact u27542
  · exact u27543

def b40504 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 227, targets := 4 },{ cop := 3, region := 194, targets := 32 }], pairs := [(0,2),(1,2),(1,5)], upper := (rows 97 138 276 13 52 99 67 195 323), lower := (rows 97 138 276 13 52 32 64 128 256), losses := [] }

theorem u40504 : Upper (D 6) (R 6) [96,136,272,5,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40504 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40505 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 138 276 13 112 39 71 135 263), lower := (rows 97 138 276 13 112 32 64 128 256), losses := [] }

theorem u40505 : Upper (D 6) (R 6) [96,136,272,5,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40505 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40506 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 138 276 14 22 97 97 225 353), lower := (rows 97 138 276 14 22 32 64 128 256), losses := [] }

theorem u40506 : Upper (D 6) (R 6) [96,136,272,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40506 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40507 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 97 138 276 14 49 103 71 199 327), lower := (rows 97 138 276 14 49 32 64 128 256), losses := [] }

theorem u40507 : Upper (D 6) (R 6) [96,136,272,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40507 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40508 : Route 9 := (fun mask => (mask,id))

def c40508 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40508 : Upper (D 6) (R 6) [96,136,272,6,34] 13 := by
  apply FastRouting.sound _ _ [96,136,272,6,34] 13 (by decide) (choices 1) [1,4,64] r40508 c40508
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27544
  · exact u27545
  · exact u27546

def r40509 : Route 9 := (fun mask => (mask,id))

def c40509 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40509 : Upper (D 6) (R 6) [96,136,272,6,36] 13 := by
  apply FastRouting.sound _ _ [96,136,272,6,36] 13 (by decide) (choices 1) [1,2,64] r40509 c40509
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27547
  · exact u27548
  · exact u27549

def b40510 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 6 },{ cop := 4, region := 1, targets := 2 }], pairs := [(0,1),(4,1),(4,2)], upper := (rows 97 138 276 14 112 39 71 135 263), lower := (rows 97 138 276 14 112 32 64 128 256), losses := [] }

theorem u40510 : Upper (D 6) (R 6) [96,136,272,6,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40510 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40511 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 138 276 41 82 39 71 135 263), lower := (rows 97 138 276 41 82 32 64 128 256), losses := [] }

theorem u40511 : Upper (D 6) (R 6) [96,136,272,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40511 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40512 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 138 276 41 84 39 71 135 263), lower := (rows 97 138 276 41 84 32 64 128 256), losses := [] }

theorem u40512 : Upper (D 6) (R 6) [96,136,272,33,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40512 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40513 : Route 9 := (fun mask => (mask,id))

def c40513 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40513 : Upper (D 6) (R 6) [96,136,272,34,66] 13 := by
  apply FastRouting.sound _ _ [96,136,272,34,66] 13 (by decide) (choices 1) [1,4] r40513 c40513
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u27550
  · exact u27551

def r40514 : Route 9 := (fun mask => (mask,id))

def c40514 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40514 : Upper (D 6) (R 6) [96,136,272,34,68] 13 := by
  apply FastRouting.sound _ _ [96,136,272,34,68] 13 (by decide) (choices 1) [1,2,4] r40514 c40514
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27552
  · exact u27553
  · exact u27554

def r40515 : Route 9 := (fun mask => (mask,id))

def c40515 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40515 : Upper (D 6) (R 6) [96,136,272,36,66] 13 := by
  apply FastRouting.sound _ _ [96,136,272,36,66] 13 (by decide) (choices 1) [1,2,4] r40515 c40515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27555
  · exact u27556
  · exact u27557

def b40516 : PairBound 9 := { available := 84, camps := [{ cop := 3, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 97 138 292 11 19 116 84 212 340), lower := (rows 97 138 292 11 19 32 64 128 256), losses := [] }

theorem u40516 : Upper (D 6) (R 6) [96,136,288,3,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40516 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40517 : Route 9 := (fun mask => (mask,id))

def c40517 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40517 : Upper (D 6) (R 6) [96,136,288,3,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3,5] 13 (by decide) (choices 1) [2,4,16,64] r40517 c40517
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27558
  · exact u27559
  · exact u27560
  · exact u27561

def r40518 : Route 9 := (fun mask => (mask,id))

def c40518 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40518 : Upper (D 6) (R 6) [96,136,288,3,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3,6] 13 (by decide) (choices 1) [1,4,16,64] r40518 c40518
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27562
  · exact u27563
  · exact u27564
  · exact u27565

def b40519 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 138 292 11 81 54 86 150 278), lower := (rows 97 138 292 11 81 32 64 128 256), losses := [] }

theorem u40519 : Upper (D 6) (R 6) [96,136,288,3,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40519 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40520 : Route 9 := (fun mask => (mask,id))

def c40520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40520 : Upper (D 6) (R 6) [96,136,288,3,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3,66] 13 (by decide) (choices 1) [1,4,16] r40520 c40520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27566
  · exact u27567
  · exact u27568

def r40521 : Route 9 := (fun mask => (mask,id))

def c40521 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40521 : Upper (D 6) (R 6) [96,136,288,3,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,3,68] 13 (by decide) (choices 1) [1,2,4,16] r40521 c40521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27569
  · exact u27570
  · exact u27571
  · exact u27572

def b40522 : PairBound 9 := { available := 86, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 356, targets := 1 }], pairs := [(1,5),(2,0),(4,5)], upper := (rows 97 138 292 13 19 118 86 214 342), lower := (rows 97 138 292 13 19 32 64 128 256), losses := [] }

theorem u40522 : Upper (D 6) (R 6) [96,136,288,5,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40523 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 16, targets := 66 },{ cop := 3, region := 210, targets := 32 }], pairs := [(1,5),(4,1),(4,6)], upper := (rows 97 138 292 13 21 114 82 210 338), lower := (rows 97 138 292 13 21 32 64 128 256), losses := [] }

theorem u40523 : Upper (D 6) (R 6) [96,136,288,5,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40523 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40524 : PairBound 9 := { available := 83, camps := [{ cop := 3, region := 210, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(1,5),(4,5)], upper := (rows 97 138 292 13 22 115 83 211 339), lower := (rows 97 138 292 13 22 32 64 128 256), losses := [] }

theorem u40524 : Upper (D 6) (R 6) [96,136,288,5,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40524 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40525 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 138 292 13 81 54 86 150 278), lower := (rows 97 138 292 13 81 32 64 128 256), losses := [] }

theorem u40525 : Upper (D 6) (R 6) [96,136,288,5,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40525 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40526 : Route 9 := (fun mask => (mask,id))

def c40526 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40526 : Upper (D 6) (R 6) [96,136,288,5,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,5,66] 13 (by decide) (choices 1) [1,2,4,16] r40526 c40526
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27573
  · exact u27574
  · exact u27575
  · exact u27576

def r40527 : Route 9 := (fun mask => (mask,id))

def c40527 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40527 : Upper (D 6) (R 6) [96,136,288,5,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,5,68] 13 (by decide) (choices 1) [1,2,16] r40527 c40527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27577
  · exact u27578
  · exact u27579

def r40528 : Route 9 := (fun mask => (mask,id))

def c40528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40528 : Upper (D 6) (R 6) [96,136,288,6,3] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6,3] 13 (by decide) (choices 1) [1,4,16,64] r40528 c40528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27580
  · exact u27581
  · exact u27582
  · exact u27583

def r40529 : Route 9 := (fun mask => (mask,id))

def c40529 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40529 : Upper (D 6) (R 6) [96,136,288,6,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6,5] 13 (by decide) (choices 1) [1,2,16,64] r40529 c40529
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27584
  · exact u27585
  · exact u27586
  · exact u27587

def b40530 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 16, targets := 97 }], pairs := [(4,0),(4,5),(4,6)], upper := (rows 97 138 292 14 22 113 81 209 337), lower := (rows 97 138 292 14 22 32 64 128 256), losses := [] }

theorem u40530 : Upper (D 6) (R 6) [96,136,288,6,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40530 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40531 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 138 292 14 81 55 87 151 279), lower := (rows 97 138 292 14 81 32 64 128 256), losses := [] }

theorem u40531 : Upper (D 6) (R 6) [96,136,288,6,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40531 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40532 : Route 9 := (fun mask => (mask,id))

def c40532 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40532 : Upper (D 6) (R 6) [96,136,288,6,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6,66] 13 (by decide) (choices 1) [1,4,16] r40532 c40532
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27588
  · exact u27589
  · exact u27590

def r40533 : Route 9 := (fun mask => (mask,id))

def c40533 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40533 : Upper (D 6) (R 6) [96,136,288,6,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,6,68] 13 (by decide) (choices 1) [1,2,16] r40533 c40533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27591
  · exact u27592
  · exact u27593

def b40534 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 138 292 25 19 102 70 198 326), lower := (rows 97 138 292 25 19 32 64 128 256), losses := [] }

theorem u40534 : Upper (D 6) (R 6) [96,136,288,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40535 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 138 292 25 21 102 70 198 326), lower := (rows 97 138 292 25 21 32 64 128 256), losses := [] }

theorem u40535 : Upper (D 6) (R 6) [96,136,288,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40536 : Route 9 := (fun mask => (mask,id))

def c40536 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40536 : Upper (D 6) (R 6) [96,136,288,17,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,17,6] 13 (by decide) (choices 1) [1,2,4,64] r40536 c40536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27594
  · exact u27595
  · exact u27596
  · exact u27597

def b40537 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 24, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 138 292 25 81 38 70 134 262), lower := (rows 97 138 292 25 81 32 64 128 256), losses := [] }

theorem u40537 : Upper (D 6) (R 6) [96,136,288,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40538 : Route 9 := (fun mask => (mask,id))

def c40538 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40538 : Upper (D 6) (R 6) [96,136,288,17,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,17,66] 13 (by decide) (choices 1) [1,2,4] r40538 c40538
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27598
  · exact u27599
  · exact u27600

def r40539 : Route 9 := (fun mask => (mask,id))

def c40539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40539 : Upper (D 6) (R 6) [96,136,288,17,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,17,68] 13 (by decide) (choices 1) [1,2,4] r40539 c40539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27601
  · exact u27602
  · exact u27603

def b40540 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 138 292 26 19 101 69 197 325), lower := (rows 97 138 292 26 19 32 64 128 256), losses := [] }

theorem u40540 : Upper (D 6) (R 6) [96,136,288,18,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40541 : Route 9 := (fun mask => (mask,id))

def c40541 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40541 : Upper (D 6) (R 6) [96,136,288,18,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,18,5] 13 (by decide) (choices 1) [1,2,4,64] r40541 c40541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27604
  · exact u27605
  · exact u27606
  · exact u27607

def b40542 : PairBound 9 := { available := 69, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 138 292 26 22 101 69 197 325), lower := (rows 97 138 292 26 22 32 64 128 256), losses := [] }

theorem u40542 : Upper (D 6) (R 6) [96,136,288,18,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40543 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 138 292 26 81 39 71 135 263), lower := (rows 97 138 292 26 81 32 64 128 256), losses := [] }

theorem u40543 : Upper (D 6) (R 6) [96,136,288,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40543 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40544 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 8, targets := 37 }], pairs := [(3,0),(3,2),(3,5)], upper := (rows 97 138 292 26 82 37 69 133 261), lower := (rows 97 138 292 26 82 32 64 128 256), losses := [] }

theorem u40544 : Upper (D 6) (R 6) [96,136,288,18,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40544 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40545 : Route 9 := (fun mask => (mask,id))

def c40545 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40545 : Upper (D 6) (R 6) [96,136,288,18,68] 13 := by
  apply FastRouting.sound _ _ [96,136,288,18,68] 13 (by decide) (choices 1) [1,2,4] r40545 c40545
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27608
  · exact u27609
  · exact u27610

def r40546 : Route 9 := (fun mask => (mask,id))

def c40546 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40546 : Upper (D 6) (R 6) [96,136,288,20,3] 13 := by
  apply FastRouting.sound _ _ [96,136,288,20,3] 13 (by decide) (choices 1) [1,2,4,64] r40546 c40546
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27611
  · exact u27612
  · exact u27613
  · exact u27614

def b40547 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 97 138 292 28 21 99 67 195 323), lower := (rows 97 138 292 28 21 32 64 128 256), losses := [] }

theorem u40547 : Upper (D 6) (R 6) [96,136,288,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40547 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40548 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 138 292 28 22 99 67 195 323), lower := (rows 97 138 292 28 22 32 64 128 256), losses := [] }

theorem u40548 : Upper (D 6) (R 6) [96,136,288,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40549 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 16, targets := 38 }], pairs := [(4,1),(4,2),(4,5)], upper := (rows 97 138 292 28 81 39 71 135 263), lower := (rows 97 138 292 28 81 32 64 128 256), losses := [] }

theorem u40549 : Upper (D 6) (R 6) [96,136,288,20,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40550 : Route 9 := (fun mask => (mask,id))

def c40550 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40550 : Upper (D 6) (R 6) [96,136,288,20,66] 13 := by
  apply FastRouting.sound _ _ [96,136,288,20,66] 13 (by decide) (choices 1) [1,2,4] r40550 c40550
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27615
  · exact u27616
  · exact u27617

def b40551 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 97 138 292 28 84 35 67 131 259), lower := (rows 97 138 292 28 84 32 64 128 256), losses := [] }

theorem u40551 : Upper (D 6) (R 6) [96,136,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b40552 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 357, targets := 2 },{ cop := 4, region := 292, targets := 64 }], pairs := [(0,1),(2,1),(2,6)], upper := (rows 97 138 292 74 19 53 85 149 277), lower := (rows 97 138 292 74 19 32 64 128 256), losses := [] }

theorem u40552 : Upper (D 6) (R 6) [96,136,288,66,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b40552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r40553 : Route 9 := (fun mask => (mask,id))

def c40553 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40553 : Upper (D 6) (R 6) [96,136,288,66,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,66,5] 13 (by decide) (choices 1) [1,2,4,16] r40553 c40553
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27618
  · exact u27619
  · exact u27620
  · exact u27621

def r40554 : Route 9 := (fun mask => (mask,id))

def c40554 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40554 : Upper (D 6) (R 6) [96,136,288,66,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,66,6] 13 (by decide) (choices 1) [1,4,16] r40554 c40554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27622
  · exact u27623
  · exact u27624

def r40555 : Route 9 := (fun mask => (mask,id))

def c40555 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40555 : Upper (D 6) (R 6) [96,136,288,68,3] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,3] 13 (by decide) (choices 1) [1,2,4,16] r40555 c40555
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u27625
  · exact u27626
  · exact u27627
  · exact u27628

def r40556 : Route 9 := (fun mask => (mask,id))

def c40556 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40556 : Upper (D 6) (R 6) [96,136,288,68,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,5] 13 (by decide) (choices 1) [1,2,16] r40556 c40556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27629
  · exact u27630
  · exact u27631

def r40557 : Route 9 := (fun mask => (mask,id))

def c40557 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40557 : Upper (D 6) (R 6) [96,136,288,68,6] 13 := by
  apply FastRouting.sound _ _ [96,136,288,68,6] 13 (by decide) (choices 1) [1,2,16] r40557 c40557
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27632
  · exact u27633
  · exact u27634

def r40558 : Route 9 := (fun mask => (mask,id))

def c40558 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40558 : Upper (D 6) (R 6) [96,136,288,80,3] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80,3] 13 (by decide) (choices 1) [1,2,4] r40558 c40558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27635
  · exact u27636
  · exact u27637

def r40559 : Route 9 := (fun mask => (mask,id))

def c40559 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u40559 : Upper (D 6) (R 6) [96,136,288,80,5] 13 := by
  apply FastRouting.sound _ _ [96,136,288,80,5] 13 (by decide) (choices 1) [1,2,4] r40559 c40559
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u27638
  · exact u27639
  · exact u27640

#print axioms u40559
end Delivery.IrregularNine14.P06
