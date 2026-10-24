import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0083
import IrregularNine14P05C0084

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8580 : PairBound 9 := { available := 311, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 76 168 311 311 375 439 311), lower := (rows 7 11 76 168 16 32 64 128 256), losses := [] }

theorem u8580 : Upper (D 5) (R 5) [6,9,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8581 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 3, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 7 11 76 392 55 55 119 183 311), lower := (rows 7 11 76 392 16 32 64 128 256), losses := [] }

theorem u8581 : Upper (D 5) (R 5) [6,9,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r8582 : Route 9 := (fun mask => (mask,id))

def c8582 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8582 : Upper (D 5) (R 5) [6,9,80,160] 13 := by
  apply FastRouting.sound _ _ [6,9,80,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r8582 c8582
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5016
  · exact u5017
  · exact u5018
  · exact u5019
  · exact u5020
  · exact u5021
  · exact u5022
  · exact u5023
  · exact u5024
  · exact u5025
  · exact u5026
  · exact u5027
  · exact u5028
  · exact u5029
  · exact u5030

def r8583 : Route 9 := (fun mask => (mask,id))

def c8583 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8583 : Upper (D 5) (R 5) [6,9,80,384] 13 := by
  apply FastRouting.sound _ _ [6,9,80,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8583 c8583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5031
  · exact u5032
  · exact u5033
  · exact u5034
  · exact u5035
  · exact u5036
  · exact u5037
  · exact u5038
  · exact u5039
  · exact u5040

theorem m8584_9 : Upper (D 5) (R 5) [6,9,96,160,9] 13 :=
  permutation_upper _ _ _ [6,9,96,160,6] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5043

theorem m8584_10 : Upper (D 5) (R 5) [6,9,96,160,10] 13 :=
  permutation_upper _ _ _ [6,9,96,160,5] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5042

theorem m8584_258 : Upper (D 5) (R 5) [6,9,96,160,258] 13 :=
  permutation_upper _ _ _ [6,9,96,160,257] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5045

theorem m8584_264 : Upper (D 5) (R 5) [6,9,96,160,264] 13 :=
  permutation_upper _ _ _ [6,9,96,160,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5046

def r8584 : Route 9 := (fun mask => (mask,id))

def c8584 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8584 : Upper (D 5) (R 5) [6,9,96,160] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r8584 c8584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5041
  · exact u5042
  · exact u5043
  · exact m8584_9
  · exact m8584_10
  · exact u5044
  · exact u5045
  · exact m8584_258
  · exact u5046
  · exact m8584_264

def r8585 : Route 9 := (fun mask => (mask,id))

def c8585 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u8585 : Upper (D 5) (R 5) [6,9,96,384] 13 := by
  apply FastRouting.sound _ _ [6,9,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r8585 c8585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5047
  · exact u5048
  · exact u5049
  · exact u5050
  · exact u5051
  · exact u5052
  · exact u5053
  · exact u5054
  · exact u5055
  · exact u5056

def b8586 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 41 506 490 490 490 490), lower := (rows 7 14 21 41 16 32 64 128 256), losses := [] }

theorem u8586 : Upper (D 5) (R 5) [6,12,17,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8587 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 42 505 489 489 489 489), lower := (rows 7 14 21 42 16 32 64 128 256), losses := [] }

theorem u8587 : Upper (D 5) (R 5) [6,12,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8588 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 73 442 426 490 426 426), lower := (rows 7 14 21 73 16 32 64 128 256), losses := [] }

theorem u8588 : Upper (D 5) (R 5) [6,12,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8589 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 74 441 425 489 425 425), lower := (rows 7 14 21 74 16 32 64 128 256), losses := [] }

theorem u8589 : Upper (D 5) (R 5) [6,12,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8590 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 104 443 427 491 427 427), lower := (rows 7 14 21 104 16 32 64 128 256), losses := [] }

theorem u8590 : Upper (D 5) (R 5) [6,12,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8591 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 21 200 315 299 363 427 299), lower := (rows 7 14 21 200 16 32 64 128 256), losses := [] }

theorem u8591 : Upper (D 5) (R 5) [6,12,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8592 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 22 41 505 489 489 489 489), lower := (rows 7 14 22 41 16 32 64 128 256), losses := [] }

theorem u8592 : Upper (D 5) (R 5) [6,12,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8593 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 22 73 441 425 489 425 425), lower := (rows 7 14 22 73 16 32 64 128 256), losses := [] }

theorem u8593 : Upper (D 5) (R 5) [6,12,18,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8593
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8594 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 22 104 441 425 489 425 425), lower := (rows 7 14 22 104 16 32 64 128 256), losses := [] }

theorem u8594 : Upper (D 5) (R 5) [6,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8595 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 488, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 22 200 313 297 361 425 297), lower := (rows 7 14 22 200 16 32 64 128 256), losses := [] }

theorem u8595 : Upper (D 5) (R 5) [6,12,18,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8596 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 28 41 499 483 483 483 483), lower := (rows 7 14 28 41 16 32 64 128 256), losses := [] }

theorem u8596 : Upper (D 5) (R 5) [6,12,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8597 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 28 73 435 419 483 419 419), lower := (rows 7 14 28 73 16 32 64 128 256), losses := [] }

theorem u8597 : Upper (D 5) (R 5) [6,12,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8598 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 28 104 435 419 483 419 419), lower := (rows 7 14 28 104 16 32 64 128 256), losses := [] }

theorem u8598 : Upper (D 5) (R 5) [6,12,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8599 : PairBound 9 := { available := 291, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 28 200 307 291 355 419 291), lower := (rows 7 14 28 200 16 32 64 128 256), losses := [] }

theorem u8599 : Upper (D 5) (R 5) [6,12,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8600 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 25 506 490 490 490 490), lower := (rows 7 14 37 25 16 32 64 128 256), losses := [] }

theorem u8600 : Upper (D 5) (R 5) [6,12,33,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8600
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8601 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 26 505 489 489 489 489), lower := (rows 7 14 37 26 16 32 64 128 256), losses := [] }

theorem u8601 : Upper (D 5) (R 5) [6,12,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8602 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 56 475 491 459 459 459), lower := (rows 7 14 37 56 16 32 64 128 256), losses := [] }

theorem u8602 : Upper (D 5) (R 5) [6,12,33,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8603 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 73 442 442 506 442 442), lower := (rows 7 14 37 73 16 32 64 128 256), losses := [] }

theorem u8603 : Upper (D 5) (R 5) [6,12,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8604 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 74 441 441 505 441 441), lower := (rows 7 14 37 74 16 32 64 128 256), losses := [] }

theorem u8604 : Upper (D 5) (R 5) [6,12,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8605 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 88 443 427 491 427 427), lower := (rows 7 14 37 88 16 32 64 128 256), losses := [] }

theorem u8605 : Upper (D 5) (R 5) [6,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8606 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 104 411 443 475 411 411), lower := (rows 7 14 37 104 16 32 64 128 256), losses := [] }

theorem u8606 : Upper (D 5) (R 5) [6,12,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8606
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8607 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 37 200 315 315 379 443 315), lower := (rows 7 14 37 200 16 32 64 128 256), losses := [] }

theorem u8607 : Upper (D 5) (R 5) [6,12,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8608 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 38 25 505 489 489 489 489), lower := (rows 7 14 38 25 16 32 64 128 256), losses := [] }

theorem u8608 : Upper (D 5) (R 5) [6,12,34,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8608
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8609 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 38 73 441 441 505 441 441), lower := (rows 7 14 38 73 16 32 64 128 256), losses := [] }

theorem u8609 : Upper (D 5) (R 5) [6,12,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8610 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 38 88 441 425 489 425 425), lower := (rows 7 14 38 88 16 32 64 128 256), losses := [] }

theorem u8610 : Upper (D 5) (R 5) [6,12,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8611 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 504, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 38 200 313 313 377 441 313), lower := (rows 7 14 38 200 16 32 64 128 256), losses := [] }

theorem u8611 : Upper (D 5) (R 5) [6,12,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8612 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 44 25 499 483 483 483 483), lower := (rows 7 14 44 25 16 32 64 128 256), losses := [] }

theorem u8612 : Upper (D 5) (R 5) [6,12,40,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8613 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 44 73 435 435 499 435 435), lower := (rows 7 14 44 73 16 32 64 128 256), losses := [] }

theorem u8613 : Upper (D 5) (R 5) [6,12,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8614 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 44 88 435 419 483 419 419), lower := (rows 7 14 44 88 16 32 64 128 256), losses := [] }

theorem u8614 : Upper (D 5) (R 5) [6,12,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8615 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 44 200 307 307 371 435 307), lower := (rows 7 14 44 200 16 32 64 128 256), losses := [] }

theorem u8615 : Upper (D 5) (R 5) [6,12,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8616 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 41 475 491 459 459 459), lower := (rows 7 14 52 41 16 32 64 128 256), losses := [] }

theorem u8616 : Upper (D 5) (R 5) [6,12,48,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8617 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 73 443 427 491 427 427), lower := (rows 7 14 52 73 16 32 64 128 256), losses := [] }

theorem u8617 : Upper (D 5) (R 5) [6,12,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8618 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 74 441 425 489 425 425), lower := (rows 7 14 52 74 16 32 64 128 256), losses := [] }

theorem u8618 : Upper (D 5) (R 5) [6,12,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8619 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 104 411 427 459 395 395), lower := (rows 7 14 52 104 16 32 64 128 256), losses := [] }

theorem u8619 : Upper (D 5) (R 5) [6,12,48,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8619
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8620 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 504, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 52 200 315 299 363 427 299), lower := (rows 7 14 52 200 16 32 64 128 256), losses := [] }

theorem u8620 : Upper (D 5) (R 5) [6,12,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8620
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8621 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 25 442 426 490 426 426), lower := (rows 7 14 69 25 16 32 64 128 256), losses := [] }

theorem u8621 : Upper (D 5) (R 5) [6,12,65,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8621
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8622 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 26 441 425 489 425 425), lower := (rows 7 14 69 26 16 32 64 128 256), losses := [] }

theorem u8622 : Upper (D 5) (R 5) [6,12,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8622
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8623 : PairBound 9 := { available := 442, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 41 442 442 506 442 442), lower := (rows 7 14 69 41 16 32 64 128 256), losses := [] }

theorem u8623 : Upper (D 5) (R 5) [6,12,65,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8623
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8624 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 42 441 441 505 441 441), lower := (rows 7 14 69 42 16 32 64 128 256), losses := [] }

theorem u8624 : Upper (D 5) (R 5) [6,12,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8624
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8625 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 56 443 427 491 427 427), lower := (rows 7 14 69 56 16 32 64 128 256), losses := [] }

theorem u8625 : Upper (D 5) (R 5) [6,12,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8625
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8626 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 137 314 314 378 442 314), lower := (rows 7 14 69 137 16 32 64 128 256), losses := [] }

theorem u8626 : Upper (D 5) (R 5) [6,12,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8626
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8627 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 138 313 313 377 441 313), lower := (rows 7 14 69 138 16 32 64 128 256), losses := [] }

theorem u8627 : Upper (D 5) (R 5) [6,12,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8627
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8628 : PairBound 9 := { available := 299, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 152 315 299 363 427 299), lower := (rows 7 14 69 152 16 32 64 128 256), losses := [] }

theorem u8628 : Upper (D 5) (R 5) [6,12,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8628
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8629 : PairBound 9 := { available := 315, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 168 315 315 379 443 315), lower := (rows 7 14 69 168 16 32 64 128 256), losses := [] }

theorem u8629 : Upper (D 5) (R 5) [6,12,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8629
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8630 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 69 392 59 59 123 187 315), lower := (rows 7 14 69 392 16 32 64 128 256), losses := [] }

theorem u8630 : Upper (D 5) (R 5) [6,12,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8630
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8631 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 25 441 425 489 425 425), lower := (rows 7 14 70 25 16 32 64 128 256), losses := [] }

theorem u8631 : Upper (D 5) (R 5) [6,12,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8631
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8632 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 41 441 441 505 441 441), lower := (rows 7 14 70 41 16 32 64 128 256), losses := [] }

theorem u8632 : Upper (D 5) (R 5) [6,12,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8632
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8633 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 56 441 425 489 425 425), lower := (rows 7 14 70 56 16 32 64 128 256), losses := [] }

theorem u8633 : Upper (D 5) (R 5) [6,12,66,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8633
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8634 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 137 313 313 377 441 313), lower := (rows 7 14 70 137 16 32 64 128 256), losses := [] }

theorem u8634 : Upper (D 5) (R 5) [6,12,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8634
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8635 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 152 313 297 361 425 297), lower := (rows 7 14 70 152 16 32 64 128 256), losses := [] }

theorem u8635 : Upper (D 5) (R 5) [6,12,66,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8635
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8636 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 168 313 313 377 441 313), lower := (rows 7 14 70 168 16 32 64 128 256), losses := [] }

theorem u8636 : Upper (D 5) (R 5) [6,12,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8636
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8637 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 14 70 392 57 57 121 185 313), lower := (rows 7 14 70 392 16 32 64 128 256), losses := [] }

theorem u8637 : Upper (D 5) (R 5) [6,12,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8637
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8638 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 25 435 419 483 419 419), lower := (rows 7 14 76 25 16 32 64 128 256), losses := [] }

theorem u8638 : Upper (D 5) (R 5) [6,12,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8638
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b8639 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 440, targets := 4 }], pairs := [(3,2),(4,2)], upper := (rows 7 14 76 41 435 435 499 435 435), lower := (rows 7 14 76 41 16 32 64 128 256), losses := [] }

theorem u8639 : Upper (D 5) (R 5) [6,12,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b8639
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u8639
end Delivery.IrregularNine14.P05
