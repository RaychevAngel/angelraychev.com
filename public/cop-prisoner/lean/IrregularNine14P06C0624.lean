import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0378
import IrregularNine14P06C0379
import IrregularNine14P06C0380

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r37440 : Route 9 := (fun mask => (mask,id))

def c37440 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37440 : Upper (D 6) (R 6) [34,129,288,6,72] 13 := by
  apply FastRouting.sound _ _ [34,129,288,6,72] 13 (by decide) (choices 1) [1,4,16,64] r37440 c37440
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22693
  · exact u22694
  · exact u22695
  · exact u22696

def b37441 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 131 292 25 26 100 68 196 324), lower := (rows 35 131 292 25 26 32 64 128 256), losses := [] }

theorem u37441 : Upper (D 6) (R 6) [34,129,288,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37441 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37442 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 324, targets := 1 }], pairs := [(1,5),(2,0),(4,0)], upper := (rows 35 131 292 25 28 102 70 198 326), lower := (rows 35 131 292 25 28 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 15 8 24 35 67 131 259), good := (rows 486 486 292 508 28 32 64 128 256) },{ target := 5, region := (rows 1 10 4 8 16 0 80 144 272), good := (rows 3 131 260 475 478 0 64 128 256) }] }

theorem u37442 : Upper (D 6) (R 6) [34,129,288,17,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37442 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37443 : Route 9 := (fun mask => (mask,id))

def c37443 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37443 : Upper (D 6) (R 6) [34,129,288,17,66] 13 := by
  apply FastRouting.sound _ _ [34,129,288,17,66] 13 (by decide) (choices 1) [4,8,64] r37443 c37443
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22697
  · exact u22698
  · exact u22699

def r37444 : Route 9 := (fun mask => (mask,id))

def c37444 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37444 : Upper (D 6) (R 6) [34,129,288,17,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,17,68] 13 (by decide) (choices 1) [2,4,8,64] r37444 c37444
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22700
  · exact u22701
  · exact u22702
  · exact u22703

def r37445 : Route 9 := (fun mask => (mask,id))

def c37445 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37445 : Upper (D 6) (R 6) [34,129,288,17,72] 13 := by
  apply FastRouting.sound _ _ [34,129,288,17,72] 13 (by decide) (choices 1) [2,4,64] r37445 c37445
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22704
  · exact u22705
  · exact u22706

def r37446 : Route 9 := (fun mask => (mask,id))

def c37446 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37446 : Upper (D 6) (R 6) [34,129,288,18,12] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,12] 13 (by decide) (choices 1) [1,4,64] r37446 c37446
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22707
  · exact u22708
  · exact u22709

def r37447 : Route 9 := (fun mask => (mask,id))

def c37447 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37447 : Upper (D 6) (R 6) [34,129,288,18,65] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,65] 13 (by decide) (choices 1) [4,8,64] r37447 c37447
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22710
  · exact u22711
  · exact u22712

def r37448 : Route 9 := (fun mask => (mask,id))

def c37448 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37448 : Upper (D 6) (R 6) [34,129,288,18,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,68] 13 (by decide) (choices 1) [1,4,8,64] r37448 c37448
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22713
  · exact u22714
  · exact u22715
  · exact u22716

def r37449 : Route 9 := (fun mask => (mask,id))

def c37449 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37449 : Upper (D 6) (R 6) [34,129,288,18,72] 13 := by
  apply FastRouting.sound _ _ [34,129,288,18,72] 13 (by decide) (choices 1) [1,4,64] r37449 c37449
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22717
  · exact u22718
  · exact u22719

def b37450 : PairBound 9 := { available := 67, camps := [{ cop := 2, region := 24, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 292 28 28 99 67 195 323), lower := (rows 35 131 292 28 28 32 64 128 256), losses := [] }

theorem u37450 : Upper (D 6) (R 6) [34,129,288,20,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37450 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37451 : Route 9 := (fun mask => (mask,id))

def c37451 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37451 : Upper (D 6) (R 6) [34,129,288,20,65] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20,65] 13 (by decide) (choices 1) [2,4,8,64] r37451 c37451
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22720
  · exact u22721
  · exact u22722
  · exact u22723

def r37452 : Route 9 := (fun mask => (mask,id))

def c37452 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37452 : Upper (D 6) (R 6) [34,129,288,20,66] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20,66] 13 (by decide) (choices 1) [1,4,8,64] r37452 c37452
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22724
  · exact u22725
  · exact u22726
  · exact u22727

def b37453 : PairBound 9 := { available := 75, camps := [{ cop := 4, region := 8, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 35 131 292 28 84 107 75 203 331), lower := (rows 35 131 292 28 84 32 64 128 256), losses := [] }

theorem u37453 : Upper (D 6) (R 6) [34,129,288,20,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37453 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37454 : Route 9 := (fun mask => (mask,id))

def c37454 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37454 : Upper (D 6) (R 6) [34,129,288,20,72] 13 := by
  apply FastRouting.sound _ _ [34,129,288,20,72] 13 (by decide) (choices 1) [1,2,4,64] r37454 c37454
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22728
  · exact u22729
  · exact u22730
  · exact u22731

def r37455 : Route 9 := (fun mask => (mask,id))

def c37455 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37455 : Upper (D 6) (R 6) [34,129,288,65,66] 13 := by
  apply FastRouting.sound _ _ [34,129,288,65,66] 13 (by decide) (choices 1) [4,8,16] r37455 c37455
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22732
  · exact u22733
  · exact u22734

def r37456 : Route 9 := (fun mask => (mask,id))

def c37456 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37456 : Upper (D 6) (R 6) [34,129,288,65,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,65,68] 13 (by decide) (choices 1) [2,4,8,16] r37456 c37456
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22735
  · exact u22736
  · exact u22737
  · exact u22738

def b37457 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 292 73 88 54 86 150 278), lower := (rows 35 131 292 73 88 32 64 128 256), losses := [] }

theorem u37457 : Upper (D 6) (R 6) [34,129,288,65,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37457 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37458 : Route 9 := (fun mask => (mask,id))

def c37458 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37458 : Upper (D 6) (R 6) [34,129,288,66,68] 13 := by
  apply FastRouting.sound _ _ [34,129,288,66,68] 13 (by decide) (choices 1) [1,4,8,16] r37458 c37458
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22739
  · exact u22740
  · exact u22741
  · exact u22742

def b37459 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 292 74 88 53 85 149 277), lower := (rows 35 131 292 74 88 32 64 128 256), losses := [] }

theorem u37459 : Upper (D 6) (R 6) [34,129,288,66,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37459 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37460 : PairBound 9 := { available := 27, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 292 76 84 59 91 155 283), lower := (rows 35 131 292 76 84 32 64 128 256), losses := [] }

theorem u37460 : Upper (D 6) (R 6) [34,129,288,68,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37460 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37461 : PairBound 9 := { available := 23, camps := [{ cop := 3, region := 16, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 35 131 292 76 88 55 87 151 279), lower := (rows 35 131 292 76 88 32 64 128 256), losses := [] }

theorem u37461 : Upper (D 6) (R 6) [34,129,288,68,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37461 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37462 : PairBound 9 := { available := 7, camps := [{ cop := 6, region := 24, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 35 131 292 88 88 39 71 135 263), lower := (rows 35 131 292 88 88 32 64 128 256), losses := [] }

theorem u37462 : Upper (D 6) (R 6) [34,129,288,80,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37462 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37463 : PairBound 9 := { available := 116, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 11 28 116 116 244 372), lower := (rows 35 131 324 11 28 32 64 128 256), losses := [] }

theorem u37463 : Upper (D 6) (R 6) [34,129,320,3,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37463 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37464 : PairBound 9 := { available := 92, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 11 52 124 92 220 348), lower := (rows 35 131 324 11 52 32 64 128 256), losses := [] }

theorem u37464 : Upper (D 6) (R 6) [34,129,320,3,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37464 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37465 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 324 11 56 116 84 212 340), lower := (rows 35 131 324 11 56 32 64 128 256), losses := [] }

theorem u37465 : Upper (D 6) (R 6) [34,129,320,3,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37465 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37466 : PairBound 9 := { available := 52, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 11 88 52 116 180 308), lower := (rows 35 131 324 11 88 32 64 128 256), losses := [] }

theorem u37466 : Upper (D 6) (R 6) [34,129,320,3,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37466 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37467 : PairBound 9 := { available := 28, camps := [{ cop := 3, region := 372, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 35 131 324 11 112 60 92 156 284), lower := (rows 35 131 324 11 112 32 64 128 256), losses := [] }

theorem u37467 : Upper (D 6) (R 6) [34,129,320,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37467 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37468 : Route 9 := (fun mask => (mask,id))

def c37468 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37468 : Upper (D 6) (R 6) [34,129,320,5,6] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,6] 13 (by decide) (choices 1) [8,16,64] r37468 c37468
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22743
  · exact u22744
  · exact u22745

def r37469 : Route 9 := (fun mask => (mask,id))

def c37469 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37469 : Upper (D 6) (R 6) [34,129,320,5,10] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,10] 13 (by decide) (choices 1) [4,16,64] r37469 c37469
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22746
  · exact u22747
  · exact u22748

def b37470 : PairBound 9 := { available := 114, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 13 28 114 114 242 370), lower := (rows 35 131 324 13 28 32 64 128 256), losses := [] }

theorem u37470 : Upper (D 6) (R 6) [34,129,320,5,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37470 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37471 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 68 },{ cop := 4, region := 1, targets := 4 }], pairs := [(0,2),(4,2),(4,6)], upper := (rows 35 131 324 13 50 124 92 220 348), lower := (rows 35 131 324 13 50 32 64 128 256), losses := [] }

theorem u37471 : Upper (D 6) (R 6) [34,129,320,5,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37471 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37472 : Route 9 := (fun mask => (mask,id))

def c37472 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37472 : Upper (D 6) (R 6) [34,129,320,5,36] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,36] 13 (by decide) (choices 1) [2,8,16,64] r37472 c37472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22749
  · exact u22750
  · exact u22751
  · exact u22752

def r37473 : Route 9 := (fun mask => (mask,id))

def c37473 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37473 : Upper (D 6) (R 6) [34,129,320,5,40] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,40] 13 (by decide) (choices 1) [2,4,16,64] r37473 c37473
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22753
  · exact u22754
  · exact u22755
  · exact u22756

def r37474 : Route 9 := (fun mask => (mask,id))

def c37474 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37474 : Upper (D 6) (R 6) [34,129,320,5,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,66] 13 (by decide) (choices 1) [4,8,16] r37474 c37474
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22757
  · exact u22758
  · exact u22759

def b37475 : PairBound 9 := { available := 58, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 13 84 58 122 186 314), lower := (rows 35 131 324 13 84 32 64 128 256), losses := [] }

theorem u37475 : Upper (D 6) (R 6) [34,129,320,5,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37475 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37476 : Route 9 := (fun mask => (mask,id))

def c37476 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37476 : Upper (D 6) (R 6) [34,129,320,5,72] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,72] 13 (by decide) (choices 1) [2,4,16] r37476 c37476
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22760
  · exact u22761
  · exact u22762

def r37477 : Route 9 := (fun mask => (mask,id))

def c37477 : Nat → Fin 9 := (fun mask => match mask with | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37477 : Upper (D 6) (R 6) [34,129,320,5,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,5,96] 13 (by decide) (choices 1) [2,4,8,16] r37477 c37477
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22763
  · exact u22764
  · exact u22765
  · exact u22766

def r37478 : Route 9 := (fun mask => (mask,id))

def c37478 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37478 : Upper (D 6) (R 6) [34,129,320,6,9] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,9] 13 (by decide) (choices 1) [4,16,64] r37478 c37478
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22767
  · exact u22768
  · exact u22769

def b37479 : PairBound 9 := { available := 113, camps := [{ cop := 3, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 14 28 113 113 241 369), lower := (rows 35 131 324 14 28 32 64 128 256), losses := [] }

theorem u37479 : Upper (D 6) (R 6) [34,129,320,6,12] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37479 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37480 : PairBound 9 := { available := 92, camps := [{ cop := 0, region := 16, targets := 70 }], pairs := [(4,1),(4,2),(4,6)], upper := (rows 35 131 324 14 49 124 92 220 348), lower := (rows 35 131 324 14 49 32 64 128 256), losses := [] }

theorem u37480 : Upper (D 6) (R 6) [34,129,320,6,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37480 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37481 : Route 9 := (fun mask => (mask,id))

def c37481 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37481 : Upper (D 6) (R 6) [34,129,320,6,36] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,36] 13 (by decide) (choices 1) [1,8,16,64] r37481 c37481
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22770
  · exact u22771
  · exact u22772
  · exact u22773

def r37482 : Route 9 := (fun mask => (mask,id))

def c37482 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37482 : Upper (D 6) (R 6) [34,129,320,6,40] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,40] 13 (by decide) (choices 1) [1,4,16,64] r37482 c37482
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22774
  · exact u22775
  · exact u22776
  · exact u22777

def r37483 : Route 9 := (fun mask => (mask,id))

def c37483 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37483 : Upper (D 6) (R 6) [34,129,320,6,65] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,65] 13 (by decide) (choices 1) [4,8,16] r37483 c37483
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22778
  · exact u22779
  · exact u22780

def b37484 : PairBound 9 := { available := 57, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 14 84 57 121 185 313), lower := (rows 35 131 324 14 84 32 64 128 256), losses := [] }

theorem u37484 : Upper (D 6) (R 6) [34,129,320,6,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37484 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37485 : Route 9 := (fun mask => (mask,id))

def c37485 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37485 : Upper (D 6) (R 6) [34,129,320,6,72] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,72] 13 (by decide) (choices 1) [1,4,16] r37485 c37485
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22781
  · exact u22782
  · exact u22783

def r37486 : Route 9 := (fun mask => (mask,id))

def c37486 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37486 : Upper (D 6) (R 6) [34,129,320,6,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,6,96] 13 (by decide) (choices 1) [1,4,8,16] r37486 c37486
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22784
  · exact u22785
  · exact u22786
  · exact u22787

def b37487 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 24, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 35 131 324 25 26 100 100 228 356), lower := (rows 35 131 324 25 26 32 64 128 256), losses := [] }

theorem u37487 : Upper (D 6) (R 6) [34,129,320,17,10] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37487 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37488 : Route 9 := (fun mask => (mask,id))

def c37488 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37488 : Upper (D 6) (R 6) [34,129,320,17,12] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,12] 13 (by decide) (choices 1) [2,4,64] r37488 c37488
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22788
  · exact u22789
  · exact u22790

def b37489 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 324 25 50 108 76 204 332), lower := (rows 35 131 324 25 50 32 64 128 256), losses := [] }

theorem u37489 : Upper (D 6) (R 6) [34,129,320,17,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37489 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37490 : Route 9 := (fun mask => (mask,id))

def c37490 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37490 : Upper (D 6) (R 6) [34,129,320,17,36] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,36] 13 (by decide) (choices 1) [2,4,8,64] r37490 c37490
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22791
  · exact u22792
  · exact u22793
  · exact u22794

def b37491 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 24, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 35 131 324 25 56 102 70 198 326), lower := (rows 35 131 324 25 56 32 64 128 256), losses := [] }

theorem u37491 : Upper (D 6) (R 6) [34,129,320,17,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37491 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37492 : Route 9 := (fun mask => (mask,id))

def c37492 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37492 : Upper (D 6) (R 6) [34,129,320,17,66] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,66] 13 (by decide) (choices 1) [4,8] r37492 c37492
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u22795
  · exact u22796

def b37493 : PairBound 9 := { available := 46, camps := [{ cop := 2, region := 16, targets := 35 }], pairs := [(4,0),(4,1),(4,5)], upper := (rows 35 131 324 25 84 46 110 174 302), lower := (rows 35 131 324 25 84 32 64 128 256), losses := [] }

theorem u37493 : Upper (D 6) (R 6) [34,129,320,17,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37493 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b37494 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 163, targets := 64 },{ cop := 0, region := 324, targets := 1 }], pairs := [(0,6),(1,6),(2,0)], upper := (rows 35 131 324 25 88 38 102 166 294), lower := (rows 35 131 324 25 88 32 64 128 256), losses := [] }

theorem u37494 : Upper (D 6) (R 6) [34,129,320,17,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37494 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37495 : Route 9 := (fun mask => (mask,id))

def c37495 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37495 : Upper (D 6) (R 6) [34,129,320,17,96] 13 := by
  apply FastRouting.sound _ _ [34,129,320,17,96] 13 (by decide) (choices 1) [2,4,8] r37495 c37495
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22797
  · exact u22798
  · exact u22799

def r37496 : Route 9 := (fun mask => (mask,id))

def c37496 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37496 : Upper (D 6) (R 6) [34,129,320,18,12] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,12] 13 (by decide) (choices 1) [1,4,64] r37496 c37496
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u22800
  · exact u22801
  · exact u22802

def b37497 : PairBound 9 := { available := 76, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 324 26 49 108 76 204 332), lower := (rows 35 131 324 26 49 32 64 128 256), losses := [] }

theorem u37497 : Upper (D 6) (R 6) [34,129,320,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37497 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r37498 : Route 9 := (fun mask => (mask,id))

def c37498 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u37498 : Upper (D 6) (R 6) [34,129,320,18,36] 13 := by
  apply FastRouting.sound _ _ [34,129,320,18,36] 13 (by decide) (choices 1) [1,4,8,64] r37498 c37498
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u22803
  · exact u22804
  · exact u22805
  · exact u22806

def b37499 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 24, targets := 68 }], pairs := [(3,2),(3,6),(4,2)], upper := (rows 35 131 324 26 56 101 69 197 325), lower := (rows 35 131 324 26 56 32 64 128 256), losses := [] }

theorem u37499 : Upper (D 6) (R 6) [34,129,320,18,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b37499 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u37499
end Delivery.IrregularNine14.P06
