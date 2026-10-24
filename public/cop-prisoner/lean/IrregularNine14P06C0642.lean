import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0407
import IrregularNine14P06C0408

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r38520 : Route 9 := (fun mask => (mask,id))

def c38520 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38520 : Upper (D 6) (R 6) [34,136,320,5,6] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,6] 13 (by decide) (choices 1) [1,16,64] r38520 c38520
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24431
  · exact u24432
  · exact u24433

def b38521 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 324 13 49 118 86 214 342), lower := (rows 35 138 324 13 49 32 64 128 256), losses := [] }

theorem u38521 : Upper (D 6) (R 6) [34,136,320,5,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38521 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38522 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 324 13 50 117 85 213 341), lower := (rows 35 138 324 13 50 32 64 128 256), losses := [] }

theorem u38522 : Upper (D 6) (R 6) [34,136,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38522 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38523 : Route 9 := (fun mask => (mask,id))

def c38523 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38523 : Upper (D 6) (R 6) [34,136,320,5,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,36] 13 (by decide) (choices 1) [1,2,16,64] r38523 c38523
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24434
  · exact u24435
  · exact u24436
  · exact u24437

def r38524 : Route 9 := (fun mask => (mask,id))

def c38524 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38524 : Upper (D 6) (R 6) [34,136,320,5,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,65] 13 (by decide) (choices 1) [2,4,16] r38524 c38524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24438
  · exact u24439
  · exact u24440

def r38525 : Route 9 := (fun mask => (mask,id))

def c38525 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38525 : Upper (D 6) (R 6) [34,136,320,5,66] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,66] 13 (by decide) (choices 1) [1,4,16] r38525 c38525
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24441
  · exact u24442
  · exact u24443

def b38526 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 13 84 51 115 179 307), lower := (rows 35 138 324 13 84 32 64 128 256), losses := [] }

theorem u38526 : Upper (D 6) (R 6) [34,136,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38526 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38527 : Route 9 := (fun mask => (mask,id))

def c38527 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38527 : Upper (D 6) (R 6) [34,136,320,5,96] 13 := by
  apply FastRouting.sound _ _ [34,136,320,5,96] 13 (by decide) (choices 1) [1,2,4,16] r38527 c38527
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24444
  · exact u24445
  · exact u24446
  · exact u24447

def r38528 : Route 9 := (fun mask => (mask,id))

def c38528 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38528 : Upper (D 6) (R 6) [34,136,320,6,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,6,5] 13 (by decide) (choices 1) [1,16,64] r38528 c38528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24448
  · exact u24449
  · exact u24450

def b38529 : PairBound 9 := { available := 85, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 324 14 49 117 85 213 341), lower := (rows 35 138 324 14 49 32 64 128 256), losses := [] }

theorem u38529 : Upper (D 6) (R 6) [34,136,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38529 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38530 : Route 9 := (fun mask => (mask,id))

def c38530 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38530 : Upper (D 6) (R 6) [34,136,320,6,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,6,36] 13 (by decide) (choices 1) [1,16,64] r38530 c38530
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24451
  · exact u24452
  · exact u24453

def r38531 : Route 9 := (fun mask => (mask,id))

def c38531 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38531 : Upper (D 6) (R 6) [34,136,320,6,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,6,65] 13 (by decide) (choices 1) [1,4,16] r38531 c38531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24454
  · exact u24455
  · exact u24456

def b38532 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 14 84 49 113 177 305), lower := (rows 35 138 324 14 84 32 64 128 256), losses := [] }

theorem u38532 : Upper (D 6) (R 6) [34,136,320,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38532 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38533 : Route 9 := (fun mask => (mask,id))

def c38533 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38533 : Upper (D 6) (R 6) [34,136,320,6,96] 13 := by
  apply FastRouting.sound _ _ [34,136,320,6,96] 13 (by decide) (choices 1) [1,4,16] r38533 c38533
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24457
  · exact u24458
  · exact u24459

def b38534 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 138 324 25 19 100 100 228 356), lower := (rows 35 138 324 25 19 32 64 128 256), losses := [] }

theorem u38534 : Upper (D 6) (R 6) [34,136,320,17,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38534 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38535 : PairBound 9 := { available := 102, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 324 25 21 102 102 230 358), lower := (rows 35 138 324 25 21 32 64 128 256), losses := [] }

theorem u38535 : Upper (D 6) (R 6) [34,136,320,17,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38535 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38536 : Route 9 := (fun mask => (mask,id))

def c38536 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38536 : Upper (D 6) (R 6) [34,136,320,17,6] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17,6] 13 (by decide) (choices 1) [1,4,64] r38536 c38536
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24460
  · exact u24461
  · exact u24462

def b38537 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 138 324 25 49 102 70 198 326), lower := (rows 35 138 324 25 49 32 64 128 256), losses := [] }

theorem u38537 : Upper (D 6) (R 6) [34,136,320,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38537 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38538 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 324 25 50 101 69 197 325), lower := (rows 35 138 324 25 50 32 64 128 256), losses := [] }

theorem u38538 : Upper (D 6) (R 6) [34,136,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38538 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38539 : Route 9 := (fun mask => (mask,id))

def c38539 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38539 : Upper (D 6) (R 6) [34,136,320,17,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17,36] 13 (by decide) (choices 1) [1,2,4,64] r38539 c38539
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24463
  · exact u24464
  · exact u24465
  · exact u24466

def b38540 : PairBound 9 := { available := 38, camps := [{ cop := 4, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 35 138 324 25 81 38 102 166 294), lower := (rows 35 138 324 25 81 32 64 128 256), losses := [] }

theorem u38540 : Upper (D 6) (R 6) [34,136,320,17,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38540 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38541 : Route 9 := (fun mask => (mask,id))

def c38541 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38541 : Upper (D 6) (R 6) [34,136,320,17,66] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17,66] 13 (by decide) (choices 1) [1,4] r38541 c38541
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24467
  · exact u24468

def b38542 : PairBound 9 := { available := 39, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 25 84 39 103 167 295), lower := (rows 35 138 324 25 84 32 64 128 256), losses := [] }

theorem u38542 : Upper (D 6) (R 6) [34,136,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38542 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38543 : Route 9 := (fun mask => (mask,id))

def c38543 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38543 : Upper (D 6) (R 6) [34,136,320,17,96] 13 := by
  apply FastRouting.sound _ _ [34,136,320,17,96] 13 (by decide) (choices 1) [1,2,4] r38543 c38543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24469
  · exact u24470
  · exact u24471

def r38544 : Route 9 := (fun mask => (mask,id))

def c38544 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38544 : Upper (D 6) (R 6) [34,136,320,18,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,18,5] 13 (by decide) (choices 1) [1,4,64] r38544 c38544
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24472
  · exact u24473
  · exact u24474

def b38545 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 324 26 49 101 69 197 325), lower := (rows 35 138 324 26 49 32 64 128 256), losses := [] }

theorem u38545 : Upper (D 6) (R 6) [34,136,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38545 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38546 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 324 26 52 101 69 197 325), lower := (rows 35 138 324 26 52 32 64 128 256), losses := [] }

theorem u38546 : Upper (D 6) (R 6) [34,136,320,18,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38546 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38547 : Route 9 := (fun mask => (mask,id))

def c38547 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38547 : Upper (D 6) (R 6) [34,136,320,18,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,18,65] 13 (by decide) (choices 1) [1,4] r38547 c38547
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u24475
  · exact u24476

def b38548 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 26 84 37 101 165 293), lower := (rows 35 138 324 26 84 32 64 128 256), losses := [] }

theorem u38548 : Upper (D 6) (R 6) [34,136,320,18,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38548 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38549 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 2 },{ cop := 0, region := 324, targets := 32 }], pairs := [(2,1),(2,5),(4,1)], upper := (rows 35 138 324 26 112 37 69 133 261), lower := (rows 35 138 324 26 112 32 64 128 256), losses := [] }

theorem u38549 : Upper (D 6) (R 6) [34,136,320,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38549 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38550 : PairBound 9 := { available := 101, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 324 28 19 101 101 229 357), lower := (rows 35 138 324 28 19 32 64 128 256), losses := [] }

theorem u38550 : Upper (D 6) (R 6) [34,136,320,20,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38550 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38551 : PairBound 9 := { available := 99, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 324 28 21 99 99 227 355), lower := (rows 35 138 324 28 21 32 64 128 256), losses := [] }

theorem u38551 : Upper (D 6) (R 6) [34,136,320,20,5] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38551 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38552 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 324 28 22 97 97 225 353), lower := (rows 35 138 324 28 22 32 64 128 256), losses := [] }

theorem u38552 : Upper (D 6) (R 6) [34,136,320,20,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38552 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38553 : PairBound 9 := { available := 71, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 324 28 49 103 71 199 327), lower := (rows 35 138 324 28 49 32 64 128 256), losses := [] }

theorem u38553 : Upper (D 6) (R 6) [34,136,320,20,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38553 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38554 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 324 28 50 101 69 197 325), lower := (rows 35 138 324 28 50 32 64 128 256), losses := [] }

theorem u38554 : Upper (D 6) (R 6) [34,136,320,20,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38554 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38555 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 324 28 52 99 67 195 323), lower := (rows 35 138 324 28 52 32 64 128 256), losses := [] }

theorem u38555 : Upper (D 6) (R 6) [34,136,320,20,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38555 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38556 : Route 9 := (fun mask => (mask,id))

def c38556 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38556 : Upper (D 6) (R 6) [34,136,320,20,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,20,65] 13 (by decide) (choices 1) [1,2,4] r38556 c38556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24477
  · exact u24478
  · exact u24479

def b38557 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 2 }], pairs := [(0,6),(1,6),(2,1)], upper := (rows 35 138 324 28 82 37 101 165 293), lower := (rows 35 138 324 28 82 32 64 128 256), losses := [] }

theorem u38557 : Upper (D 6) (R 6) [34,136,320,20,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38557 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38558 : PairBound 9 := { available := 35, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 138 324 28 84 35 99 163 291), lower := (rows 35 138 324 28 84 32 64 128 256), losses := [] }

theorem u38558 : Upper (D 6) (R 6) [34,136,320,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38558 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38559 : PairBound 9 := { available := 7, camps := [{ cop := 3, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 32 }], pairs := [(0,6),(1,6),(2,5)], upper := (rows 35 138 324 28 112 39 71 135 263), lower := (rows 35 138 324 28 112 32 64 128 256), losses := [] }

theorem u38559 : Upper (D 6) (R 6) [34,136,320,20,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38559 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38560 : PairBound 9 := { available := 85, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 0, region := 340, targets := 32 }], pairs := [(2,5),(4,2),(4,6)], upper := (rows 35 138 324 44 19 117 85 213 341), lower := (rows 35 138 324 44 19 32 64 128 256), losses := [] }

theorem u38560 : Upper (D 6) (R 6) [34,136,320,36,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38561 : Route 9 := (fun mask => (mask,id))

def c38561 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38561 : Upper (D 6) (R 6) [34,136,320,36,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,36,5] 13 (by decide) (choices 1) [1,2,16,64] r38561 c38561
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24480
  · exact u24481
  · exact u24482
  · exact u24483

def b38562 : PairBound 9 := { available := 81, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 4, region := 97, targets := 4 }], pairs := [(0,2),(2,5),(4,5)], upper := (rows 35 138 324 44 22 113 81 209 337), lower := (rows 35 138 324 44 22 32 64 128 256), losses := [] }

theorem u38562 : Upper (D 6) (R 6) [34,136,320,36,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38563 : Route 9 := (fun mask => (mask,id))

def c38563 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38563 : Upper (D 6) (R 6) [34,136,320,36,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,36,65] 13 (by decide) (choices 1) [1,2,4,16] r38563 c38563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24484
  · exact u24485
  · exact u24486
  · exact u24487

def r38564 : Route 9 := (fun mask => (mask,id))

def c38564 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38564 : Upper (D 6) (R 6) [34,136,320,36,66] 13 := by
  apply FastRouting.sound _ _ [34,136,320,36,66] 13 (by decide) (choices 1) [1,4,16] r38564 c38564
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24488
  · exact u24489
  · exact u24490

def b38565 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 44 84 51 83 147 275), lower := (rows 35 138 324 44 84 32 64 128 256), losses := [] }

theorem u38565 : Upper (D 6) (R 6) [34,136,320,36,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38565 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38566 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 138 324 56 19 101 69 197 325), lower := (rows 35 138 324 56 19 32 64 128 256), losses := [] }

theorem u38566 : Upper (D 6) (R 6) [34,136,320,48,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38567 : Route 9 := (fun mask => (mask,id))

def c38567 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38567 : Upper (D 6) (R 6) [34,136,320,48,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,48,5] 13 (by decide) (choices 1) [1,2,4,64] r38567 c38567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24491
  · exact u24492
  · exact u24493
  · exact u24494

def b38568 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 138 324 56 22 101 69 197 325), lower := (rows 35 138 324 56 22 32 64 128 256), losses := [] }

theorem u38568 : Upper (D 6) (R 6) [34,136,320,48,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38568 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38569 : Route 9 := (fun mask => (mask,id))

def c38569 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38569 : Upper (D 6) (R 6) [34,136,320,48,65] 13 := by
  apply FastRouting.sound _ _ [34,136,320,48,65] 13 (by decide) (choices 1) [1,2,4] r38569 c38569
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24495
  · exact u24496
  · exact u24497

def b38570 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 340, targets := 32 },{ cop := 0, region := 324, targets := 2 }], pairs := [(2,1),(2,5),(4,5)], upper := (rows 35 138 324 56 82 37 69 133 261), lower := (rows 35 138 324 56 82 32 64 128 256), losses := [] }

theorem u38570 : Upper (D 6) (R 6) [34,136,320,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38571 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 138 324 56 84 39 71 135 263), lower := (rows 35 138 324 56 84 32 64 128 256), losses := [] }

theorem u38571 : Upper (D 6) (R 6) [34,136,320,48,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38572 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 16, targets := 100 }], pairs := [(4,2),(4,5),(4,6)], upper := (rows 35 138 324 73 19 52 116 180 308), lower := (rows 35 138 324 73 19 32 64 128 256), losses := [] }

theorem u38572 : Upper (D 6) (R 6) [34,136,320,65,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38572 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38573 : Route 9 := (fun mask => (mask,id))

def c38573 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38573 : Upper (D 6) (R 6) [34,136,320,65,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65,5] 13 (by decide) (choices 1) [2,4,16] r38573 c38573
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24498
  · exact u24499
  · exact u24500

def r38574 : Route 9 := (fun mask => (mask,id))

def c38574 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38574 : Upper (D 6) (R 6) [34,136,320,65,6] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65,6] 13 (by decide) (choices 1) [1,4,16] r38574 c38574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24501
  · exact u24502
  · exact u24503

def b38575 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 138 324 73 49 54 86 150 278), lower := (rows 35 138 324 73 49 32 64 128 256), losses := [] }

theorem u38575 : Upper (D 6) (R 6) [34,136,320,65,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38575 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b38576 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 138 324 73 50 53 85 149 277), lower := (rows 35 138 324 73 50 32 64 128 256), losses := [] }

theorem u38576 : Upper (D 6) (R 6) [34,136,320,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38576 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r38577 : Route 9 := (fun mask => (mask,id))

def c38577 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38577 : Upper (D 6) (R 6) [34,136,320,65,36] 13 := by
  apply FastRouting.sound _ _ [34,136,320,65,36] 13 (by decide) (choices 1) [1,2,4,16] r38577 c38577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u24504
  · exact u24505
  · exact u24506
  · exact u24507

def r38578 : Route 9 := (fun mask => (mask,id))

def c38578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u38578 : Upper (D 6) (R 6) [34,136,320,66,5] 13 := by
  apply FastRouting.sound _ _ [34,136,320,66,5] 13 (by decide) (choices 1) [1,4,16] r38578 c38578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u24508
  · exact u24509
  · exact u24510

def b38579 : PairBound 9 := { available := 21, camps := [{ cop := 4, region := 462, targets := 32 }], pairs := [(1,5),(2,5),(3,5)], upper := (rows 35 138 324 74 49 53 85 149 277), lower := (rows 35 138 324 74 49 32 64 128 256), losses := [] }

theorem u38579 : Upper (D 6) (R 6) [34,136,320,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b38579 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u38579
end Delivery.IrregularNine14.P06
