import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P04C0003
import IrregularNine14P04C0004
import IrregularNine14P04C0005
import IrregularNine14P04C0006
import IrregularNine14P04C0007
import IrregularNine14P04C0008

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b600 : PairBound 9 := { available := 410, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 37 73 410 442 474 410 410), lower := (rows 7 22 37 73 16 32 64 128 256), losses := [] }

theorem u600 : Upper (D 4) (R 4) [6,20,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b600
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b601 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 37 200 283 315 347 411 283), lower := (rows 7 22 37 200 16 32 64 128 256), losses := [] }

theorem u601 : Upper (D 4) (R 4) [6,20,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b601
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b602 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 44 73 411 443 475 411 411), lower := (rows 7 22 44 73 16 32 64 128 256), losses := [] }

theorem u602 : Upper (D 4) (R 4) [6,20,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b602
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b603 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 472, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 44 200 283 315 347 411 283), lower := (rows 7 22 44 200 16 32 64 128 256), losses := [] }

theorem u603 : Upper (D 4) (R 4) [6,20,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b603
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b604 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 456, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 52 73 411 427 459 395 395), lower := (rows 7 22 52 73 16 32 64 128 256), losses := [] }

theorem u604 : Upper (D 4) (R 4) [6,20,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b604
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b605 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 456, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 52 200 283 299 331 395 267), lower := (rows 7 22 52 200 16 32 64 128 256), losses := [] }

theorem u605 : Upper (D 4) (R 4) [6,20,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b605
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b606 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 100 137 283 315 347 411 283), lower := (rows 7 22 100 137 16 32 64 128 256), losses := [] }

theorem u606 : Upper (D 4) (R 4) [6,20,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b606
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b607 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 22 100 392 27 59 91 155 283), lower := (rows 7 22 100 392 16 32 64 128 256), losses := [] }

theorem u607 : Upper (D 4) (R 4) [6,20,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b607
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b608 : PairBound 9 := { available := 455, camps := [{ cop := 0, region := 464, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 28 41 471 487 455 455 455), lower := (rows 7 26 28 41 16 32 64 128 256), losses := [] }

theorem u608 : Upper (D 4) (R 4) [6,24,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b608
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b609 : PairBound 9 := { available := 391, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 28 104 407 423 455 391 391), lower := (rows 7 26 28 104 16 32 64 128 256), losses := [] }

theorem u609 : Upper (D 4) (R 4) [6,24,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b609
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b610 : PairBound 9 := { available := 462, camps := [{ cop := 1, region := 485, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 25 478 494 462 462 462), lower := (rows 7 26 37 25 16 32 64 128 256), losses := [] }

theorem u610 : Upper (D 4) (R 4) [6,24,33,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b610
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b611 : PairBound 9 := { available := 461, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 37 26 477 493 461 461 461), lower := (rows 7 26 37 26 16 32 64 128 256), losses := [] }

theorem u611 : Upper (D 4) (R 4) [6,24,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b611
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b612 : PairBound 9 := { available := 459, camps := [{ cop := 1, region := 485, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 28 475 491 459 459 459), lower := (rows 7 26 37 28 16 32 64 128 256), losses := [] }

theorem u612 : Upper (D 4) (R 4) [6,24,33,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b612
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m613_6 : Upper (D 4) (R 4) [6,24,33,65,6] 13 :=
  permutation_upper _ _ _ [6,9,48,80,6] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u315

theorem m613_10 : Upper (D 4) (R 4) [6,24,33,65,10] 13 :=
  permutation_upper _ _ _ [6,5,40,17,72] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u228

theorem m613_12 : Upper (D 4) (R 4) [6,24,33,65,12] 13 :=
  permutation_upper _ _ _ [6,12,48,80,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u379

def r613 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c613 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u613 : Upper (D 4) (R 4) [6,24,33,65] 13 := by
  apply FastRouting.sound _ _ [6,24,33,65] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r613 c613
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m613_6
  · exact m613_10
  · exact m613_12
  · exact u404
  · exact u405
  · exact u406
  · exact u407

theorem m614_5 : Upper (D 4) (R 4) [6,24,33,66,5] 13 :=
  permutation_upper _ _ _ [6,12,34,17,72] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u354

theorem m614_9 : Upper (D 4) (R 4) [6,24,33,66,9] 13 :=
  permutation_upper _ _ _ [6,12,33,17,72] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u339

theorem m614_12 : Upper (D 4) (R 4) [6,24,33,66,12] 13 :=
  permutation_upper _ _ _ [6,12,33,80,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u345

theorem m614_129 : Upper (D 4) (R 4) [6,24,33,66,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u404

def r614 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c614 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u614 : Upper (D 4) (R 4) [6,24,33,66] 13 := by
  apply FastRouting.sound _ _ [6,24,33,66] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r614 c614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m614_5
  · exact m614_9
  · exact m614_12
  · exact m614_129
  · exact u408
  · exact u409
  · exact u410

theorem m615_3 : Upper (D 4) (R 4) [6,24,33,68,3] 13 :=
  permutation_upper _ _ _ [6,9,18,48,68] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u258

theorem m615_9 : Upper (D 4) (R 4) [6,24,33,68,9] 13 :=
  permutation_upper _ _ _ [6,12,48,17,72] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u369

theorem m615_10 : Upper (D 4) (R 4) [6,24,33,68,10] 13 :=
  permutation_upper _ _ _ [6,5,40,80,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u232

theorem m615_129 : Upper (D 4) (R 4) [6,24,33,68,129] 13 :=
  permutation_upper _ _ _ [6,24,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u405

theorem m615_130 : Upper (D 4) (R 4) [6,24,33,68,130] 13 :=
  permutation_upper _ _ _ [6,24,33,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u408

def r615 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c615 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u615 : Upper (D 4) (R 4) [6,24,33,68] 13 := by
  apply FastRouting.sound _ _ [6,24,33,68] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r615 c615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m615_3
  · exact m615_9
  · exact m615_10
  · exact m615_129
  · exact m615_130
  · exact u411
  · exact u412

def b616 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 421, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 37 88 415 431 463 399 399), lower := (rows 7 26 37 88 16 32 64 128 256), losses := [] }

theorem u616 : Upper (D 4) (R 4) [6,24,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b616
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m617_3 : Upper (D 4) (R 4) [6,24,33,192,3] 13 :=
  permutation_upper _ _ _ [6,9,18,96,132] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u262

theorem m617_5 : Upper (D 4) (R 4) [6,24,33,192,5] 13 :=
  permutation_upper _ _ _ [6,12,34,17,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u355

theorem m617_6 : Upper (D 4) (R 4) [6,24,33,192,6] 13 :=
  permutation_upper _ _ _ [6,9,48,192,6] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u322

theorem m617_9 : Upper (D 4) (R 4) [6,24,33,192,9] 13 :=
  permutation_upper _ _ _ [6,12,96,17,136] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u388

theorem m617_10 : Upper (D 4) (R 4) [6,24,33,192,10] 13 :=
  permutation_upper _ _ _ [6,5,96,17,136] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u239

theorem m617_12 : Upper (D 4) (R 4) [6,24,33,192,12] 13 :=
  permutation_upper _ _ _ [6,12,96,144,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u395

theorem m617_257 : Upper (D 4) (R 4) [6,24,33,192,257] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u407

theorem m617_258 : Upper (D 4) (R 4) [6,24,33,192,258] 13 :=
  permutation_upper _ _ _ [6,24,33,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u410

theorem m617_260 : Upper (D 4) (R 4) [6,24,33,192,260] 13 :=
  permutation_upper _ _ _ [6,24,33,68,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u412

theorem m617_264 : Upper (D 4) (R 4) [6,24,33,192,264] 13 :=
  permutation_upper _ _ _ [6,24,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u414

def r617 : Route 9 := (fun mask => (mask,id))

def c617 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u617 : Upper (D 4) (R 4) [6,24,33,192] 13 := by
  apply FastRouting.sound _ _ [6,24,33,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r617 c617
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m617_3
  · exact m617_5
  · exact m617_6
  · exact m617_9
  · exact m617_10
  · exact m617_12
  · exact m617_257
  · exact m617_258
  · exact m617_260
  · exact m617_264

def b618 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 73 413 445 477 413 413), lower := (rows 7 26 38 73 16 32 64 128 256), losses := [] }

theorem u618 : Upper (D 4) (R 4) [6,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b618
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b619 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 26 38 200 285 317 349 413 285), lower := (rows 7 26 38 200 16 32 64 128 256), losses := [] }

theorem u619 : Upper (D 4) (R 4) [6,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b619
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b620 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 400, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 73 407 439 471 407 407), lower := (rows 7 26 44 73 16 32 64 128 256), losses := [] }

theorem u620 : Upper (D 4) (R 4) [6,24,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b620
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b621 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 400, targets := 4 }], pairs := [(4,2)], upper := (rows 7 26 44 76 403 435 467 403 403), lower := (rows 7 26 44 76 16 32 64 128 256), losses := [] }

theorem u621 : Upper (D 4) (R 4) [6,24,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b621
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b622 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 26 44 200 279 311 343 407 279), lower := (rows 7 26 44 200 16 32 64 128 256), losses := [] }

theorem u622 : Upper (D 4) (R 4) [6,24,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b622
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b623 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 7 26 52 73 415 431 463 399 399), lower := (rows 7 26 52 73 16 32 64 128 256), losses := [] }

theorem u623 : Upper (D 4) (R 4) [6,24,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b623
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b624 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 7 26 52 200 287 303 335 399 271), lower := (rows 7 26 52 200 16 32 64 128 256), losses := [] }

theorem u624 : Upper (D 4) (R 4) [6,24,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b624
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b625 : PairBound 9 := { available := 399, camps := [{ cop := 1, region := 485, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 100 25 415 431 463 399 399), lower := (rows 7 26 100 25 16 32 64 128 256), losses := [] }

theorem u625 : Upper (D 4) (R 4) [6,24,96,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b625
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b626 : PairBound 9 := { available := 397, camps := [{ cop := 4, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 7 26 100 26 413 429 461 397 397), lower := (rows 7 26 100 26 16 32 64 128 256), losses := [] }

theorem u626 : Upper (D 4) (R 4) [6,24,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b626
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b627 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 485, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 100 28 411 427 459 395 395), lower := (rows 7 26 100 28 16 32 64 128 256), losses := [] }

theorem u627 : Upper (D 4) (R 4) [6,24,96,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b627
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m628_3 : Upper (D 4) (R 4) [6,24,96,129,3] 13 :=
  permutation_upper _ _ _ [6,9,18,36,192] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u256

theorem m628_5 : Upper (D 4) (R 4) [6,24,96,129,5] 13 :=
  permutation_upper _ _ _ [6,12,96,17,130] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u387

theorem m628_6 : Upper (D 4) (R 4) [6,24,96,129,6] 13 :=
  permutation_upper _ _ _ [6,9,48,192,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u323

theorem m628_9 : Upper (D 4) (R 4) [6,24,96,129,9] 13 :=
  permutation_upper _ _ _ [6,12,40,17,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u364

theorem m628_10 : Upper (D 4) (R 4) [6,24,96,129,10] 13 :=
  permutation_upper _ _ _ [6,5,40,17,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u229

theorem m628_12 : Upper (D 4) (R 4) [6,24,96,129,12] 13 :=
  permutation_upper _ _ _ [6,12,48,192,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u383

def r628 : Route 9 := (fun mask => (mask,id))

def c628 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u628 : Upper (D 4) (R 4) [6,24,96,129] 13 := by
  apply FastRouting.sound _ _ [6,24,96,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r628 c628
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m628_3
  · exact m628_5
  · exact m628_6
  · exact m628_9
  · exact m628_10
  · exact m628_12
  · exact u433
  · exact u434
  · exact u435
  · exact u436

theorem m629_5 : Upper (D 4) (R 4) [6,24,96,130,5] 13 :=
  permutation_upper _ _ _ [6,12,96,17,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u388

theorem m629_9 : Upper (D 4) (R 4) [6,24,96,130,9] 13 :=
  permutation_upper _ _ _ [6,12,33,17,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u340

theorem m629_12 : Upper (D 4) (R 4) [6,24,96,130,12] 13 :=
  permutation_upper _ _ _ [6,12,33,192,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u350

theorem m629_257 : Upper (D 4) (R 4) [6,24,96,130,257] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u434

def r629 : Route 9 := (fun mask => (mask,id))

def c629 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u629 : Upper (D 4) (R 4) [6,24,96,130] 13 := by
  apply FastRouting.sound _ _ [6,24,96,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r629 c629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m629_5
  · exact m629_9
  · exact m629_12
  · exact m629_257
  · exact u437
  · exact u438

theorem m630_3 : Upper (D 4) (R 4) [6,24,96,132,3] 13 :=
  permutation_upper _ _ _ [6,9,18,48,192] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u260

theorem m630_9 : Upper (D 4) (R 4) [6,24,96,132,9] 13 :=
  permutation_upper _ _ _ [6,12,48,17,192] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u370

theorem m630_10 : Upper (D 4) (R 4) [6,24,96,132,10] 13 :=
  permutation_upper _ _ _ [6,5,40,192,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u236

theorem m630_257 : Upper (D 4) (R 4) [6,24,96,132,257] 13 :=
  permutation_upper _ _ _ [6,24,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u435

theorem m630_258 : Upper (D 4) (R 4) [6,24,96,132,258] 13 :=
  permutation_upper _ _ _ [6,24,96,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u437

def r630 : Route 9 := (fun mask => (mask,id))

def c630 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u630 : Upper (D 4) (R 4) [6,24,96,132] 13 := by
  apply FastRouting.sound _ _ [6,24,96,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r630 c630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m630_3
  · exact m630_9
  · exact m630_10
  · exact m630_257
  · exact m630_258
  · exact u439

def b631 : PairBound 9 := { available := 271, camps := [{ cop := 1, region := 357, targets := 16 }], pairs := [(0,4)], upper := (rows 7 26 100 152 287 303 335 399 271), lower := (rows 7 26 100 152 16 32 64 128 256), losses := [] }

theorem u631 : Upper (D 4) (R 4) [6,24,96,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b631
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m632_3 : Upper (D 4) (R 4) [6,24,96,384,3] 13 :=
  permutation_upper _ _ _ [6,9,18,96,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u264

theorem m632_5 : Upper (D 4) (R 4) [6,24,96,384,5] 13 :=
  permutation_upper _ _ _ [6,12,96,17,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u389

theorem m632_6 : Upper (D 4) (R 4) [6,24,96,384,6] 13 :=
  permutation_upper _ _ _ [6,9,96,384,6] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u332

theorem m632_9 : Upper (D 4) (R 4) [6,24,96,384,9] 13 :=
  permutation_upper _ _ _ [6,12,96,17,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u389

theorem m632_10 : Upper (D 4) (R 4) [6,24,96,384,10] 13 :=
  permutation_upper _ _ _ [6,5,96,17,384] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u240

theorem m632_12 : Upper (D 4) (R 4) [6,24,96,384,12] 13 :=
  permutation_upper _ _ _ [6,12,96,384,9] (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u399

def r632 : Route 9 := (fun mask => (mask,id))

def c632 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u632 : Upper (D 4) (R 4) [6,24,96,384] 13 := by
  apply FastRouting.sound _ _ [6,24,96,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r632 c632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m632_3
  · exact m632_5
  · exact m632_6
  · exact m632_9
  · exact m632_10
  · exact m632_12

def b633 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 138 284 316 348 412 284), lower := (rows 7 35 69 138 16 32 64 128 256), losses := [] }

theorem u633 : Upper (D 4) (R 4) [6,33,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b633
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b634 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 69 392 30 62 94 158 286), lower := (rows 7 35 69 392 16 32 64 128 256), losses := [] }

theorem u634 : Upper (D 4) (R 4) [6,33,65,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b634
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b635 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 137 284 316 348 412 284), lower := (rows 7 35 70 137 16 32 64 128 256), losses := [] }

theorem u635 : Upper (D 4) (R 4) [6,33,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b635
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b636 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 140 281 313 345 409 281), lower := (rows 7 35 70 140 16 32 64 128 256), losses := [] }

theorem u636 : Upper (D 4) (R 4) [6,33,66,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b636
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b637 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 70 392 29 61 93 157 285), lower := (rows 7 35 70 392 16 32 64 128 256), losses := [] }

theorem u637 : Upper (D 4) (R 4) [6,33,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b637
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b638 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 76 14 409 441 473 409 409), lower := (rows 7 35 76 14 16 32 64 128 256), losses := [] }

theorem u638 : Upper (D 4) (R 4) [6,33,72,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b638
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m639_6 : Upper (D 4) (R 4) [6,33,72,17,6] 13 :=
  permutation_upper _ _ _ [6,24,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u400

theorem m639_10 : Upper (D 4) (R 4) [6,33,72,17,10] 13 :=
  permutation_upper _ _ _ [6,9,24,36,65] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u271

theorem m639_12 : Upper (D 4) (R 4) [6,33,72,17,12] 13 :=
  permutation_upper _ _ _ [6,9,24,33,68] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u266

theorem m639_130 : Upper (D 4) (R 4) [6,33,72,17,130] 13 :=
  permutation_upper _ _ _ [6,24,40,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u421

theorem m639_132 : Upper (D 4) (R 4) [6,33,72,17,132] 13 :=
  permutation_upper _ _ _ [6,24,40,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u418

theorem m639_136 : Upper (D 4) (R 4) [6,33,72,17,136] 13 :=
  permutation_upper _ _ _ [6,24,33,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u404

theorem m639_384 : Upper (D 4) (R 4) [6,33,72,17,384] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u434

def r639 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c639 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u639 : Upper (D 4) (R 4) [6,33,72,17] 13 := by
  apply FastRouting.sound _ _ [6,33,72,17] 13 (by decide) (choices 2) [6,10,12,130,132,136,384] r639 c639
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m639_6
  · exact m639_10
  · exact m639_12
  · exact m639_130
  · exact m639_132
  · exact m639_136
  · exact m639_384

theorem m640_5 : Upper (D 4) (R 4) [6,33,72,18,5] 13 :=
  permutation_upper _ _ _ [6,12,48,66,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u375

theorem m640_9 : Upper (D 4) (R 4) [6,33,72,18,9] 13 :=
  permutation_upper _ _ _ [6,9,24,36,66] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u272

theorem m640_12 : Upper (D 4) (R 4) [6,33,72,18,12] 13 :=
  permutation_upper _ _ _ [6,9,34,80,12] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u295

def r640 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c640 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u640 : Upper (D 4) (R 4) [6,33,72,18] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r640 c640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m640_5
  · exact m640_9
  · exact m640_12
  · exact u454
  · exact u455
  · exact u456
  · exact u457

theorem m641_3 : Upper (D 4) (R 4) [6,33,72,20,3] 13 :=
  permutation_upper _ _ _ [6,12,34,80,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u357

theorem m641_9 : Upper (D 4) (R 4) [6,33,72,20,9] 13 :=
  permutation_upper _ _ _ [6,9,24,34,68] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u269

theorem m641_10 : Upper (D 4) (R 4) [6,33,72,20,10] 13 :=
  permutation_upper _ _ _ [6,9,33,80,12] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u284

theorem m641_129 : Upper (D 4) (R 4) [6,33,72,20,129] 13 :=
  permutation_upper _ _ _ [6,33,72,18,136] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u456

theorem m641_136 : Upper (D 4) (R 4) [6,33,72,20,136] 13 :=
  permutation_upper _ _ _ [6,33,65,18,136] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u442

def r641 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c641 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u641 : Upper (D 4) (R 4) [6,33,72,20] 13 := by
  apply FastRouting.sound _ _ [6,33,72,20] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r641 c641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m641_3
  · exact m641_9
  · exact m641_10
  · exact m641_129
  · exact u458
  · exact m641_136
  · exact u459

def r642 : Route 9 := (fun mask => (mask,id))

def c642 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u642 : Upper (D 4) (R 4) [6,33,72,129] 13 := by
  apply FastRouting.sound _ _ [6,33,72,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r642 c642
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u460
  · exact u461
  · exact u462
  · exact u463
  · exact u464
  · exact u465

theorem m643_5 : Upper (D 4) (R 4) [6,33,72,130,5] 13 :=
  permutation_upper _ _ _ [6,12,48,66,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u377

theorem m643_9 : Upper (D 4) (R 4) [6,33,72,130,9] 13 :=
  permutation_upper _ _ _ [6,24,40,66,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u422

def r643 : Route 9 := (fun mask => (mask,id))

def c643 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u643 : Upper (D 4) (R 4) [6,33,72,130] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r643 c643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m643_5
  · exact m643_9
  · exact u466
  · exact u467
  · exact u468
  · exact u469

theorem m644_3 : Upper (D 4) (R 4) [6,33,72,132,3] 13 :=
  permutation_upper _ _ _ [6,12,34,80,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u359

theorem m644_9 : Upper (D 4) (R 4) [6,33,72,132,9] 13 :=
  permutation_upper _ _ _ [6,24,40,68,130] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u425

def r644 : Route 9 := (fun mask => (mask,id))

def c644 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u644 : Upper (D 4) (R 4) [6,33,72,132] 13 := by
  apply FastRouting.sound _ _ [6,33,72,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r644 c644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m644_3
  · exact m644_9
  · exact u470
  · exact u471
  · exact u472
  · exact u473

theorem m645_3 : Upper (D 4) (R 4) [6,33,72,144,3] 13 :=
  permutation_upper _ _ _ [6,12,34,80,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u358

theorem m645_5 : Upper (D 4) (R 4) [6,33,72,144,5] 13 :=
  permutation_upper _ _ _ [6,12,48,66,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u376

theorem m645_9 : Upper (D 4) (R 4) [6,33,72,144,9] 13 :=
  permutation_upper _ _ _ [6,24,33,66,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u408

theorem m645_10 : Upper (D 4) (R 4) [6,33,72,144,10] 13 :=
  permutation_upper _ _ _ [6,33,72,20,130] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u458

theorem m645_12 : Upper (D 4) (R 4) [6,33,72,144,12] 13 :=
  permutation_upper _ _ _ [6,33,66,20,136] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u447

def r645 : Route 9 := (fun mask => (mask,id))

def c645 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u645 : Upper (D 4) (R 4) [6,33,72,144] 13 := by
  apply FastRouting.sound _ _ [6,33,72,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r645 c645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m645_3
  · exact m645_5
  · exact u474
  · exact m645_9
  · exact m645_10
  · exact m645_12
  · exact u475
  · exact u476
  · exact u477
  · exact u478

theorem m646_3 : Upper (D 4) (R 4) [6,33,72,384,3] 13 :=
  permutation_upper _ _ _ [6,12,34,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u360

theorem m646_5 : Upper (D 4) (R 4) [6,33,72,384,5] 13 :=
  permutation_upper _ _ _ [6,12,48,66,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u378

theorem m646_9 : Upper (D 4) (R 4) [6,33,72,384,9] 13 :=
  permutation_upper _ _ _ [6,24,96,130,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u437

def r646 : Route 9 := (fun mask => (mask,id))

def c646 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u646 : Upper (D 4) (R 4) [6,33,72,384] 13 := by
  apply FastRouting.sound _ _ [6,33,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r646 c646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m646_3
  · exact m646_5
  · exact u479
  · exact m646_9
  · exact u480
  · exact u481

def b647 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 84 14 409 441 473 409 409), lower := (rows 7 35 84 14 16 32 64 128 256), losses := [] }

theorem u647 : Upper (D 4) (R 4) [6,33,80,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b647
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m648_6 : Upper (D 4) (R 4) [6,33,80,129,6] 13 :=
  permutation_upper _ _ _ [6,33,72,6,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u452

theorem m648_10 : Upper (D 4) (R 4) [6,33,80,129,10] 13 :=
  permutation_upper _ _ _ [6,33,72,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u454

theorem m648_12 : Upper (D 4) (R 4) [6,33,80,129,12] 13 :=
  permutation_upper _ _ _ [6,33,72,18,136] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u456

theorem m648_258 : Upper (D 4) (R 4) [6,33,80,129,258] 13 :=
  permutation_upper _ _ _ [6,33,72,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u467

theorem m648_260 : Upper (D 4) (R 4) [6,33,80,129,260] 13 :=
  permutation_upper _ _ _ [6,33,72,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u471

theorem m648_264 : Upper (D 4) (R 4) [6,33,80,129,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u475

def r648 : Route 9 := (fun mask => (mask,id))

def c648 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u648 : Upper (D 4) (R 4) [6,33,80,129] 13 := by
  apply FastRouting.sound _ _ [6,33,80,129] 13 (by decide) (choices 2) [6,10,12,258,260,264] r648 c648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m648_6
  · exact m648_10
  · exact m648_12
  · exact m648_258
  · exact m648_260
  · exact m648_264

theorem m649_5 : Upper (D 4) (R 4) [6,33,80,130,5] 13 :=
  permutation_upper _ _ _ [6,12,33,66,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u343

theorem m649_9 : Upper (D 4) (R 4) [6,33,80,130,9] 13 :=
  permutation_upper _ _ _ [6,24,40,66,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u421

theorem m649_12 : Upper (D 4) (R 4) [6,33,80,130,12] 13 :=
  permutation_upper _ _ _ [6,33,72,20,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u458

theorem m649_257 : Upper (D 4) (R 4) [6,33,80,130,257] 13 :=
  permutation_upper _ _ _ [6,33,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u463

theorem m649_260 : Upper (D 4) (R 4) [6,33,80,130,260] 13 :=
  permutation_upper _ _ _ [6,33,72,132,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u472

theorem m649_264 : Upper (D 4) (R 4) [6,33,80,130,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u476

def r649 : Route 9 := (fun mask => (mask,id))

def c649 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u649 : Upper (D 4) (R 4) [6,33,80,130] 13 := by
  apply FastRouting.sound _ _ [6,33,80,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r649 c649
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m649_5
  · exact m649_9
  · exact m649_12
  · exact m649_257
  · exact m649_260
  · exact m649_264

theorem m650_3 : Upper (D 4) (R 4) [6,33,80,384,3] 13 :=
  permutation_upper _ _ _ [6,12,34,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u356

theorem m650_5 : Upper (D 4) (R 4) [6,33,80,384,5] 13 :=
  permutation_upper _ _ _ [6,12,33,66,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u344

theorem m650_6 : Upper (D 4) (R 4) [6,33,80,384,6] 13 :=
  permutation_upper _ _ _ [6,33,72,6,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u453

theorem m650_9 : Upper (D 4) (R 4) [6,33,80,384,9] 13 :=
  permutation_upper _ _ _ [6,24,96,129,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u434

theorem m650_10 : Upper (D 4) (R 4) [6,33,80,384,10] 13 :=
  permutation_upper _ _ _ [6,33,72,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u457

theorem m650_12 : Upper (D 4) (R 4) [6,33,80,384,12] 13 :=
  permutation_upper _ _ _ [6,33,72,20,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u459

def r650 : Route 9 := (fun mask => (mask,id))

def c650 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u650 : Upper (D 4) (R 4) [6,33,80,384] 13 := by
  apply FastRouting.sound _ _ [6,33,80,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r650 c650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m650_3
  · exact m650_5
  · exact m650_6
  · exact m650_9
  · exact m650_10
  · exact m650_12

def b651 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 14 281 313 345 409 281), lower := (rows 7 35 196 14 16 32 64 128 256), losses := [] }

theorem u651 : Upper (D 4) (R 4) [6,33,192,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b651
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m652_6 : Upper (D 4) (R 4) [6,33,192,17,6] 13 :=
  permutation_upper _ _ _ [6,24,24,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u402

theorem m652_10 : Upper (D 4) (R 4) [6,33,192,17,10] 13 :=
  permutation_upper _ _ _ [6,9,24,36,192] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u273

theorem m652_12 : Upper (D 4) (R 4) [6,33,192,17,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,132] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u279

theorem m652_258 : Upper (D 4) (R 4) [6,33,192,17,258] 13 :=
  permutation_upper _ _ _ [6,24,40,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u423

theorem m652_260 : Upper (D 4) (R 4) [6,33,192,17,260] 13 :=
  permutation_upper _ _ _ [6,24,40,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u431

theorem m652_264 : Upper (D 4) (R 4) [6,33,192,17,264] 13 :=
  permutation_upper _ _ _ [6,24,33,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u410

def r652 : Route 9 := (fun mask => (mask,id))

def c652 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u652 : Upper (D 4) (R 4) [6,33,192,17] 13 := by
  apply FastRouting.sound _ _ [6,33,192,17] 13 (by decide) (choices 2) [6,10,12,258,260,264] r652 c652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m652_6
  · exact m652_10
  · exact m652_12
  · exact m652_258
  · exact m652_260
  · exact m652_264

theorem m653_5 : Upper (D 4) (R 4) [6,33,192,18,5] 13 :=
  permutation_upper _ _ _ [6,12,96,130,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u392

theorem m653_9 : Upper (D 4) (R 4) [6,33,192,18,9] 13 :=
  permutation_upper _ _ _ [6,9,24,36,192] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u273

theorem m653_12 : Upper (D 4) (R 4) [6,33,192,18,12] 13 :=
  permutation_upper _ _ _ [6,9,48,192,12] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u325

theorem m653_264 : Upper (D 4) (R 4) [6,33,192,18,264] 13 :=
  permutation_upper _ _ _ [6,33,72,20,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u459

def r653 : Route 9 := (fun mask => (mask,id))

def c653 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u653 : Upper (D 4) (R 4) [6,33,192,18] 13 := by
  apply FastRouting.sound _ _ [6,33,192,18] 13 (by decide) (choices 2) [5,9,12,257,260,264] r653 c653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m653_5
  · exact m653_9
  · exact m653_12
  · exact u484
  · exact u485
  · exact m653_264

theorem m654_3 : Upper (D 4) (R 4) [6,33,192,20,3] 13 :=
  permutation_upper _ _ _ [6,12,34,192,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u361

theorem m654_9 : Upper (D 4) (R 4) [6,33,192,20,9] 13 :=
  permutation_upper _ _ _ [6,9,24,96,132] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u279

theorem m654_10 : Upper (D 4) (R 4) [6,33,192,20,10] 13 :=
  permutation_upper _ _ _ [6,9,48,192,12] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u325

def r654 : Route 9 := (fun mask => (mask,id))

def c654 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u654 : Upper (D 4) (R 4) [6,33,192,20] 13 := by
  apply FastRouting.sound _ _ [6,33,192,20] 13 (by decide) (choices 2) [3,9,10,257,258,264] r654 c654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m654_3
  · exact m654_9
  · exact m654_10
  · exact u486
  · exact u487
  · exact u488

theorem m655_6 : Upper (D 4) (R 4) [6,33,192,257,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u482

theorem m655_10 : Upper (D 4) (R 4) [6,33,192,257,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u484

theorem m655_12 : Upper (D 4) (R 4) [6,33,192,257,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u486

def r655 : Route 9 := (fun mask => (mask,id))

def c655 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u655 : Upper (D 4) (R 4) [6,33,192,257] 13 := by
  apply FastRouting.sound _ _ [6,33,192,257] 13 (by decide) (choices 2) [6,10,12] r655 c655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m655_6
  · exact m655_10
  · exact m655_12

theorem m656_5 : Upper (D 4) (R 4) [6,33,192,258,5] 13 :=
  permutation_upper _ _ _ [6,12,96,130,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u394

theorem m656_9 : Upper (D 4) (R 4) [6,33,192,258,9] 13 :=
  permutation_upper _ _ _ [6,24,40,66,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u423

theorem m656_12 : Upper (D 4) (R 4) [6,33,192,258,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u487

def r656 : Route 9 := (fun mask => (mask,id))

def c656 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u656 : Upper (D 4) (R 4) [6,33,192,258] 13 := by
  apply FastRouting.sound _ _ [6,33,192,258] 13 (by decide) (choices 2) [5,9,12] r656 c656
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m656_5
  · exact m656_9
  · exact m656_12

theorem m657_3 : Upper (D 4) (R 4) [6,33,192,260,3] 13 :=
  permutation_upper _ _ _ [6,12,34,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u363

theorem m657_9 : Upper (D 4) (R 4) [6,33,192,260,9] 13 :=
  permutation_upper _ _ _ [6,24,40,192,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u431

theorem m657_10 : Upper (D 4) (R 4) [6,33,192,260,10] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u485

def r657 : Route 9 := (fun mask => (mask,id))

def c657 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u657 : Upper (D 4) (R 4) [6,33,192,260] 13 := by
  apply FastRouting.sound _ _ [6,33,192,260] 13 (by decide) (choices 2) [3,9,10] r657 c657
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m657_3
  · exact m657_9
  · exact m657_10

theorem m658_3 : Upper (D 4) (R 4) [6,33,192,272,3] 13 :=
  permutation_upper _ _ _ [6,12,34,192,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u362

theorem m658_5 : Upper (D 4) (R 4) [6,33,192,272,5] 13 :=
  permutation_upper _ _ _ [6,12,96,130,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u393

theorem m658_6 : Upper (D 4) (R 4) [6,33,192,272,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u483

theorem m658_9 : Upper (D 4) (R 4) [6,33,192,272,9] 13 :=
  permutation_upper _ _ _ [6,24,33,66,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u410

theorem m658_10 : Upper (D 4) (R 4) [6,33,192,272,10] 13 :=
  permutation_upper _ _ _ [6,33,72,20,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u459

theorem m658_12 : Upper (D 4) (R 4) [6,33,192,272,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u488

def r658 : Route 9 := (fun mask => (mask,id))

def c658 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u658 : Upper (D 4) (R 4) [6,33,192,272] 13 := by
  apply FastRouting.sound _ _ [6,33,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r658 c658
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m658_3
  · exact m658_5
  · exact m658_6
  · exact m658_9
  · exact m658_10
  · exact m658_12

def b659 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 25 409 441 473 409 409), lower := (rows 7 38 70 25 16 32 64 128 256), losses := [] }

theorem u659 : Upper (D 4) (R 4) [6,36,66,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b659
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u659
end Delivery.IrregularNine14.P04
