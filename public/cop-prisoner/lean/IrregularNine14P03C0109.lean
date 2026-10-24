import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0067
import IrregularNine14P03C0068
import IrregularNine14P03C0069

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6540 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 296 211 243 211 211 467), lower := (rows 97 7 13 296 16 32 64 128 256), losses := [] }

theorem u6540 : Upper (D 3) (R 3) [96,5,9,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6540
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6541 : PairBound 9 := { available := 243, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 13 392 243 243 243 243 499), lower := (rows 97 7 13 392 16 32 64 128 256), losses := [] }

theorem u6541 : Upper (D 3) (R 3) [96,5,9,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6542 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 25 497 481 481 481 481), lower := (rows 97 7 14 25 16 32 64 128 256), losses := [] }

theorem u6542 : Upper (D 3) (R 3) [96,5,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6542
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6543 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 41 465 497 465 465 465), lower := (rows 97 7 14 41 16 32 64 128 256), losses := [] }

theorem u6543 : Upper (D 3) (R 3) [96,5,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6543
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6544 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 56 465 481 449 449 449), lower := (rows 97 7 14 56 16 32 64 128 256), losses := [] }

theorem u6544 : Upper (D 3) (R 3) [96,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6544
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6545 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 14 104 401 433 465 401 401), lower := (rows 97 7 14 104 16 32 64 128 256), losses := [] }

theorem u6545 : Upper (D 3) (R 3) [96,5,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6546 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 137 497 497 497 497 497), lower := (rows 97 7 14 137 16 32 64 128 256), losses := [] }

theorem u6546 : Upper (D 3) (R 3) [96,5,10,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6546
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6547 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6547 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6547 : Upper (D 3) (R 3) [96,5,10,144] 13 := by
  apply FastRouting.sound _ _ [96,5,10,144] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r6547 c6547
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4114
  · exact u4115
  · exact u4116
  · exact u4117
  · exact u4118
  · exact u4119
  · exact u4120

def b6548 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 168 465 497 465 465 465), lower := (rows 97 7 14 168 16 32 64 128 256), losses := [] }

theorem u6548 : Upper (D 3) (R 3) [96,5,10,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6548
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6549 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 14 265 241 241 241 241 497), lower := (rows 97 7 14 265 16 32 64 128 256), losses := [] }

theorem u6549 : Upper (D 3) (R 3) [96,5,10,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6550 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6550 : Upper (D 3) (R 3) [96,5,10,272] 13 := by
  apply FastRouting.sound _ _ [96,5,10,272] 13 (by decide) (choices 2) [33,96,129,160] r6550 c6550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4128
  · exact u4129
  · exact u4130
  · exact u4131

def b6551 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 14 296 209 241 209 209 465), lower := (rows 97 7 14 296 16 32 64 128 256), losses := [] }

theorem u6551 : Upper (D 3) (R 3) [96,5,10,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6551
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6552 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6552 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6552 : Upper (D 3) (R 3) [96,5,10,384] 13 := by
  apply FastRouting.sound _ _ [96,5,10,384] 13 (by decide) (choices 2) [33,96,129,160] r6552 c6552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4134
  · exact u4135
  · exact u4136
  · exact u4137

def b6553 : PairBound 9 := { available := 457, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 42 473 489 457 457 457), lower := (rows 97 7 21 42 16 32 64 128 256), losses := [] }

theorem u6553 : Upper (D 3) (R 3) [96,5,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6554 : PairBound 9 := { available := 490, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 137 506 490 490 490 490), lower := (rows 97 7 21 137 16 32 64 128 256), losses := [] }

theorem u6554 : Upper (D 3) (R 3) [96,5,17,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6554
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6555 : PairBound 9 := { available := 489, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 138 505 489 489 489 489), lower := (rows 97 7 21 138 16 32 64 128 256), losses := [] }

theorem u6555 : Upper (D 3) (R 3) [96,5,17,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6556 : PairBound 9 := { available := 459, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 168 475 491 459 459 459), lower := (rows 97 7 21 168 16 32 64 128 256), losses := [] }

theorem u6556 : Upper (D 3) (R 3) [96,5,17,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6557 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 265 250 234 234 234 490), lower := (rows 97 7 21 265 16 32 64 128 256), losses := [] }

theorem u6557 : Upper (D 3) (R 3) [96,5,17,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6557
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6558 : PairBound 9 := { available := 233, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 266 249 233 233 233 489), lower := (rows 97 7 21 266 16 32 64 128 256), losses := [] }

theorem u6558 : Upper (D 3) (R 3) [96,5,17,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6558
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6559 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 296 219 235 203 203 459), lower := (rows 97 7 21 296 16 32 64 128 256), losses := [] }

theorem u6559 : Upper (D 3) (R 3) [96,5,17,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6559
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6560 : PairBound 9 := { available := 235, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 21 392 251 235 235 235 491), lower := (rows 97 7 21 392 16 32 64 128 256), losses := [] }

theorem u6560 : Upper (D 3) (R 3) [96,5,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6560
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6561_9 : Upper (D 3) (R 3) [96,5,18,129,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4091

theorem m6561_33 : Upper (D 3) (R 3) [96,5,18,129,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4096

theorem m6561_40 : Upper (D 3) (R 3) [96,5,18,129,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4101

theorem m6561_96 : Upper (D 3) (R 3) [96,5,18,129,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4106

theorem m6561_129 : Upper (D 3) (R 3) [96,5,18,129,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4109

theorem m6561_136 : Upper (D 3) (R 3) [96,5,18,129,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4116

theorem m6561_160 : Upper (D 3) (R 3) [96,5,18,129,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4121

theorem m6561_257 : Upper (D 3) (R 3) [96,5,18,129,257] 13 :=
  permutation_upper _ _ _ [96,5,10,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4126

theorem m6561_264 : Upper (D 3) (R 3) [96,5,18,129,264] 13 :=
  permutation_upper _ _ _ [96,5,10,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4130

theorem m6561_288 : Upper (D 3) (R 3) [96,5,18,129,288] 13 :=
  permutation_upper _ _ _ [96,5,10,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4132

theorem m6561_384 : Upper (D 3) (R 3) [96,5,18,129,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4136

def r6561 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6561 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u6561 : Upper (D 3) (R 3) [96,5,18,129] 13 := by
  apply FastRouting.sound _ _ [96,5,18,129] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r6561 c6561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6561_9
  · exact m6561_33
  · exact m6561_40
  · exact m6561_96
  · exact m6561_129
  · exact m6561_136
  · exact m6561_160
  · exact m6561_257
  · exact m6561_264
  · exact m6561_288
  · exact m6561_384

theorem m6562_9 : Upper (D 3) (R 3) [96,5,18,160,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4092

theorem m6562_65 : Upper (D 3) (R 3) [96,5,18,160,65] 13 :=
  permutation_upper _ _ _ [96,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4097

theorem m6562_72 : Upper (D 3) (R 3) [96,5,18,160,72] 13 :=
  permutation_upper _ _ _ [96,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4102

theorem m6562_129 : Upper (D 3) (R 3) [96,5,18,160,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4110

theorem m6562_136 : Upper (D 3) (R 3) [96,5,18,160,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4117

theorem m6562_192 : Upper (D 3) (R 3) [96,5,18,160,192] 13 :=
  permutation_upper _ _ _ [96,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4122

theorem m6562_257 : Upper (D 3) (R 3) [96,5,18,160,257] 13 :=
  permutation_upper _ _ _ [96,5,10,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4127

theorem m6562_264 : Upper (D 3) (R 3) [96,5,18,160,264] 13 :=
  permutation_upper _ _ _ [96,5,10,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4131

theorem m6562_320 : Upper (D 3) (R 3) [96,5,18,160,320] 13 :=
  permutation_upper _ _ _ [96,5,10,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4133

theorem m6562_384 : Upper (D 3) (R 3) [96,5,18,160,384] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4137

def r6562 : Route 9 := (fun mask => (mask,id))

def c6562 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6562 : Upper (D 3) (R 3) [96,5,18,160] 13 := by
  apply FastRouting.sound _ _ [96,5,18,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6562 c6562
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6562_9
  · exact m6562_65
  · exact m6562_72
  · exact m6562_129
  · exact m6562_136
  · exact m6562_192
  · exact m6562_257
  · exact m6562_264
  · exact m6562_320
  · exact m6562_384

theorem m6563_9 : Upper (D 3) (R 3) [96,5,18,257,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4093

theorem m6563_33 : Upper (D 3) (R 3) [96,5,18,257,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4098

theorem m6563_40 : Upper (D 3) (R 3) [96,5,18,257,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4103

theorem m6563_96 : Upper (D 3) (R 3) [96,5,18,257,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4107

theorem m6563_129 : Upper (D 3) (R 3) [96,5,18,257,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4111

theorem m6563_136 : Upper (D 3) (R 3) [96,5,18,257,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4118

theorem m6563_160 : Upper (D 3) (R 3) [96,5,18,257,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4123

def r6563 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6563 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6563 : Upper (D 3) (R 3) [96,5,18,257] 13 := by
  apply FastRouting.sound _ _ [96,5,18,257] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r6563 c6563
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6563_9
  · exact m6563_33
  · exact m6563_40
  · exact m6563_96
  · exact m6563_129
  · exact m6563_136
  · exact m6563_160

theorem m6564_9 : Upper (D 3) (R 3) [96,5,18,288,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4094

theorem m6564_65 : Upper (D 3) (R 3) [96,5,18,288,65] 13 :=
  permutation_upper _ _ _ [96,5,10,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4099

theorem m6564_72 : Upper (D 3) (R 3) [96,5,18,288,72] 13 :=
  permutation_upper _ _ _ [96,5,10,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4104

theorem m6564_129 : Upper (D 3) (R 3) [96,5,18,288,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4112

theorem m6564_136 : Upper (D 3) (R 3) [96,5,18,288,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4119

theorem m6564_192 : Upper (D 3) (R 3) [96,5,18,288,192] 13 :=
  permutation_upper _ _ _ [96,5,10,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4124

def r6564 : Route 9 := (fun mask => (mask,id))

def c6564 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6564 : Upper (D 3) (R 3) [96,5,18,288] 13 := by
  apply FastRouting.sound _ _ [96,5,18,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6564 c6564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6564_9
  · exact m6564_65
  · exact m6564_72
  · exact m6564_129
  · exact m6564_136
  · exact m6564_192

theorem m6565_9 : Upper (D 3) (R 3) [96,5,18,384,9] 13 :=
  permutation_upper _ _ _ [96,5,10,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4095

theorem m6565_33 : Upper (D 3) (R 3) [96,5,18,384,33] 13 :=
  permutation_upper _ _ _ [96,5,10,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4100

theorem m6565_40 : Upper (D 3) (R 3) [96,5,18,384,40] 13 :=
  permutation_upper _ _ _ [96,5,10,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4105

theorem m6565_96 : Upper (D 3) (R 3) [96,5,18,384,96] 13 :=
  permutation_upper _ _ _ [96,5,10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4108

theorem m6565_129 : Upper (D 3) (R 3) [96,5,18,384,129] 13 :=
  permutation_upper _ _ _ [96,5,10,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4113

theorem m6565_136 : Upper (D 3) (R 3) [96,5,18,384,136] 13 :=
  permutation_upper _ _ _ [96,5,10,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4120

theorem m6565_160 : Upper (D 3) (R 3) [96,5,18,384,160] 13 :=
  permutation_upper _ _ _ [96,5,10,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4125

def r6565 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6565 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6565 : Upper (D 3) (R 3) [96,5,18,384] 13 := by
  apply FastRouting.sound _ _ [96,5,18,384] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r6565 c6565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6565_9
  · exact m6565_33
  · exact m6565_40
  · exact m6565_96
  · exact m6565_129
  · exact m6565_136
  · exact m6565_160

def b6566 : PairBound 9 := { available := 451, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 28 41 467 483 451 451 451), lower := (rows 97 7 28 41 16 32 64 128 256), losses := [] }

theorem u6566 : Upper (D 3) (R 3) [96,5,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6567 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 42 465 481 449 449 449), lower := (rows 97 7 28 42 16 32 64 128 256), losses := [] }

theorem u6567 : Upper (D 3) (R 3) [96,5,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6568 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 28 104 403 419 451 387 387), lower := (rows 97 7 28 104 16 32 64 128 256), losses := [] }

theorem u6568 : Upper (D 3) (R 3) [96,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6568
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6569_3 : Upper (D 3) (R 3) [96,5,24,129,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4033

theorem m6569_33 : Upper (D 3) (R 3) [96,5,24,129,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4138

theorem m6569_34 : Upper (D 3) (R 3) [96,5,24,129,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4143

theorem m6569_96 : Upper (D 3) (R 3) [96,5,24,129,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4148

def r6569 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6569 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6569 : Upper (D 3) (R 3) [96,5,24,129] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r6569 c6569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6569_3
  · exact m6569_33
  · exact m6569_34
  · exact m6569_96
  · exact u4153
  · exact u4154
  · exact u4155
  · exact u4156
  · exact u4157
  · exact u4158
  · exact u4159

theorem m6570_33 : Upper (D 3) (R 3) [96,5,24,130,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4139

theorem m6570_96 : Upper (D 3) (R 3) [96,5,24,130,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4149

theorem m6570_129 : Upper (D 3) (R 3) [96,5,24,130,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4154

def r6570 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6570 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6570 : Upper (D 3) (R 3) [96,5,24,130] 13 := by
  apply FastRouting.sound _ _ [96,5,24,130] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r6570 c6570
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6570_33
  · exact m6570_96
  · exact m6570_129
  · exact u4160
  · exact u4161
  · exact u4162
  · exact u4163

def b6571 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 168 467 483 451 451 451), lower := (rows 97 7 28 168 16 32 64 128 256), losses := [] }

theorem u6571 : Upper (D 3) (R 3) [96,5,24,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6571
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6572_3 : Upper (D 3) (R 3) [96,5,24,257,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4035

theorem m6572_33 : Upper (D 3) (R 3) [96,5,24,257,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4140

theorem m6572_34 : Upper (D 3) (R 3) [96,5,24,257,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4145

theorem m6572_96 : Upper (D 3) (R 3) [96,5,24,257,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4150

theorem m6572_129 : Upper (D 3) (R 3) [96,5,24,257,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4156

theorem m6572_130 : Upper (D 3) (R 3) [96,5,24,257,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4161

theorem m6572_160 : Upper (D 3) (R 3) [96,5,24,257,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4165

def r6572 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6572 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6572 : Upper (D 3) (R 3) [96,5,24,257] 13 := by
  apply FastRouting.sound _ _ [96,5,24,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6572 c6572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6572_3
  · exact m6572_33
  · exact m6572_34
  · exact m6572_96
  · exact m6572_129
  · exact m6572_130
  · exact m6572_160

theorem m6573_33 : Upper (D 3) (R 3) [96,5,24,258,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4141

theorem m6573_96 : Upper (D 3) (R 3) [96,5,24,258,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4151

theorem m6573_129 : Upper (D 3) (R 3) [96,5,24,258,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4157

theorem m6573_160 : Upper (D 3) (R 3) [96,5,24,258,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4166

def r6573 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6573 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6573 : Upper (D 3) (R 3) [96,5,24,258] 13 := by
  apply FastRouting.sound _ _ [96,5,24,258] 13 (by decide) (choices 2) [33,96,129,160] r6573 c6573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m6573_33
  · exact m6573_96
  · exact m6573_129
  · exact m6573_160

def b6574 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 28 296 211 227 195 195 451), lower := (rows 97 7 28 296 16 32 64 128 256), losses := [] }

theorem u6574 : Upper (D 3) (R 3) [96,5,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6574
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6575_3 : Upper (D 3) (R 3) [96,5,24,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4037

theorem m6575_33 : Upper (D 3) (R 3) [96,5,24,384,33] 13 :=
  permutation_upper _ _ _ [96,5,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4142

theorem m6575_34 : Upper (D 3) (R 3) [96,5,24,384,34] 13 :=
  permutation_upper _ _ _ [96,5,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4147

theorem m6575_96 : Upper (D 3) (R 3) [96,5,24,384,96] 13 :=
  permutation_upper _ _ _ [96,5,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4152

theorem m6575_129 : Upper (D 3) (R 3) [96,5,24,384,129] 13 :=
  permutation_upper _ _ _ [96,5,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4159

theorem m6575_130 : Upper (D 3) (R 3) [96,5,24,384,130] 13 :=
  permutation_upper _ _ _ [96,5,24,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4163

theorem m6575_160 : Upper (D 3) (R 3) [96,5,24,384,160] 13 :=
  permutation_upper _ _ _ [96,5,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4168

def r6575 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6575 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6575 : Upper (D 3) (R 3) [96,5,24,384] 13 := by
  apply FastRouting.sound _ _ [96,5,24,384] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6575 c6575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6575_3
  · exact m6575_33
  · exact m6575_34
  · exact m6575_96
  · exact m6575_129
  · exact m6575_130
  · exact m6575_160

def b6576 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 26 473 489 457 457 457), lower := (rows 97 7 37 26 16 32 64 128 256), losses := [] }

theorem u6576 : Upper (D 3) (R 3) [96,5,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6577 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 37 74 409 441 473 409 409), lower := (rows 97 7 37 74 16 32 64 128 256), losses := [] }

theorem u6577 : Upper (D 3) (R 3) [96,5,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6578 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 137 474 506 474 474 474), lower := (rows 97 7 37 137 16 32 64 128 256), losses := [] }

theorem u6578 : Upper (D 3) (R 3) [96,5,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6579 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 138 473 505 473 473 473), lower := (rows 97 7 37 138 16 32 64 128 256), losses := [] }

theorem u6579 : Upper (D 3) (R 3) [96,5,33,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6579
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6580 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 200 411 443 475 411 411), lower := (rows 97 7 37 200 16 32 64 128 256), losses := [] }

theorem u6580 : Upper (D 3) (R 3) [96,5,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6581 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 265 218 250 218 218 474), lower := (rows 97 7 37 265 16 32 64 128 256), losses := [] }

theorem u6581 : Upper (D 3) (R 3) [96,5,33,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6582 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 266 217 249 217 217 473), lower := (rows 97 7 37 266 16 32 64 128 256), losses := [] }

theorem u6582 : Upper (D 3) (R 3) [96,5,33,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6583 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 328 155 187 219 155 411), lower := (rows 97 7 37 328 16 32 64 128 256), losses := [] }

theorem u6583 : Upper (D 3) (R 3) [96,5,33,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6583
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6584 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 37 392 219 251 219 219 475), lower := (rows 97 7 37 392 16 32 64 128 256), losses := [] }

theorem u6584 : Upper (D 3) (R 3) [96,5,33,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6584
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6585 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 137 473 505 473 473 473), lower := (rows 97 7 38 137 16 32 64 128 256), losses := [] }

theorem u6585 : Upper (D 3) (R 3) [96,5,34,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6586 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 200 409 441 473 409 409), lower := (rows 97 7 38 200 16 32 64 128 256), losses := [] }

theorem u6586 : Upper (D 3) (R 3) [96,5,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6587 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 265 217 249 217 217 473), lower := (rows 97 7 38 265 16 32 64 128 256), losses := [] }

theorem u6587 : Upper (D 3) (R 3) [96,5,34,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6587
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6588 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 328 153 185 217 153 409), lower := (rows 97 7 38 328 16 32 64 128 256), losses := [] }

theorem u6588 : Upper (D 3) (R 3) [96,5,34,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6588
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6589 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 38 392 217 249 217 217 473), lower := (rows 97 7 38 392 16 32 64 128 256), losses := [] }

theorem u6589 : Upper (D 3) (R 3) [96,5,34,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6590 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 26 465 481 449 449 449), lower := (rows 97 7 44 26 16 32 64 128 256), losses := [] }

theorem u6590 : Upper (D 3) (R 3) [96,5,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6591 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 44 74 401 433 465 401 401), lower := (rows 97 7 44 74 16 32 64 128 256), losses := [] }

theorem u6591 : Upper (D 3) (R 3) [96,5,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6592 : PairBound 9 := { available := 467, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 137 467 499 467 467 467), lower := (rows 97 7 44 137 16 32 64 128 256), losses := [] }

theorem u6592 : Upper (D 3) (R 3) [96,5,40,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6593 : PairBound 9 := { available := 465, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 138 465 497 465 465 465), lower := (rows 97 7 44 138 16 32 64 128 256), losses := [] }

theorem u6593 : Upper (D 3) (R 3) [96,5,40,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6593
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6594 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 200 403 435 467 403 403), lower := (rows 97 7 44 200 16 32 64 128 256), losses := [] }

theorem u6594 : Upper (D 3) (R 3) [96,5,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6595 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 265 211 243 211 211 467), lower := (rows 97 7 44 265 16 32 64 128 256), losses := [] }

theorem u6595 : Upper (D 3) (R 3) [96,5,40,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6596 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 266 209 241 209 209 465), lower := (rows 97 7 44 266 16 32 64 128 256), losses := [] }

theorem u6596 : Upper (D 3) (R 3) [96,5,40,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6597 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 328 147 179 211 147 403), lower := (rows 97 7 44 328 16 32 64 128 256), losses := [] }

theorem u6597 : Upper (D 3) (R 3) [96,5,40,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6598 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 44 392 211 243 211 211 467), lower := (rows 97 7 44 392 16 32 64 128 256), losses := [] }

theorem u6598 : Upper (D 3) (R 3) [96,5,40,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6599 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 74 409 425 457 393 393), lower := (rows 97 7 52 74 16 32 64 128 256), losses := [] }

theorem u6599 : Upper (D 3) (R 3) [96,5,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6599
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6599
end Delivery.IrregularNine14.P03
