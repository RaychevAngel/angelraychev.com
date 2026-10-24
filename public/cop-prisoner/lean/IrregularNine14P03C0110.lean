import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0066
import IrregularNine14P03C0067
import IrregularNine14P03C0069
import IrregularNine14P03C0070
import IrregularNine14P03C0071
import IrregularNine14P03C0072
import IrregularNine14P03C0073
import IrregularNine14P03C0074

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6600 : PairBound 9 := { available := 459, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 137 475 491 459 459 459), lower := (rows 97 7 52 137 16 32 64 128 256), losses := [] }

theorem u6600 : Upper (D 3) (R 3) [96,5,48,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6601 : PairBound 9 := { available := 457, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 138 473 489 457 457 457), lower := (rows 97 7 52 138 16 32 64 128 256), losses := [] }

theorem u6601 : Upper (D 3) (R 3) [96,5,48,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6602 : PairBound 9 := { available := 395, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 200 411 427 459 395 395), lower := (rows 97 7 52 200 16 32 64 128 256), losses := [] }

theorem u6602 : Upper (D 3) (R 3) [96,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6603 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 265 219 235 203 203 459), lower := (rows 97 7 52 265 16 32 64 128 256), losses := [] }

theorem u6603 : Upper (D 3) (R 3) [96,5,48,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6604 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 266 217 233 201 201 457), lower := (rows 97 7 52 266 16 32 64 128 256), losses := [] }

theorem u6604 : Upper (D 3) (R 3) [96,5,48,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6605 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 328 155 171 203 139 395), lower := (rows 97 7 52 328 16 32 64 128 256), losses := [] }

theorem u6605 : Upper (D 3) (R 3) [96,5,48,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6606 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 52 392 219 235 203 203 459), lower := (rows 97 7 52 392 16 32 64 128 256), losses := [] }

theorem u6606 : Upper (D 3) (R 3) [96,5,48,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6607 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 26 409 425 457 393 393), lower := (rows 97 7 100 26 16 32 64 128 256), losses := [] }

theorem u6607 : Upper (D 3) (R 3) [96,5,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6608 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 137 411 443 475 411 411), lower := (rows 97 7 100 137 16 32 64 128 256), losses := [] }

theorem u6608 : Upper (D 3) (R 3) [96,5,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6609 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 138 409 441 473 409 409), lower := (rows 97 7 100 138 16 32 64 128 256), losses := [] }

theorem u6609 : Upper (D 3) (R 3) [96,5,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6610 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 265 155 187 219 155 411), lower := (rows 97 7 100 265 16 32 64 128 256), losses := [] }

theorem u6610 : Upper (D 3) (R 3) [96,5,96,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6611 : PairBound 9 := { available := 153, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 266 153 185 217 153 409), lower := (rows 97 7 100 266 16 32 64 128 256), losses := [] }

theorem u6611 : Upper (D 3) (R 3) [96,5,96,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6612 : PairBound 9 := { available := 155, camps := [{ cop := 0, region := 6, targets := 128 }], pairs := [(1,7)], upper := (rows 97 7 100 392 155 187 219 155 411), lower := (rows 97 7 100 392 16 32 64 128 256), losses := [] }

theorem u6612 : Upper (D 3) (R 3) [96,5,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6613 : PairBound 9 := { available := 489, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 26 505 489 489 489 489), lower := (rows 97 7 133 26 16 32 64 128 256), losses := [] }

theorem u6613 : Upper (D 3) (R 3) [96,5,129,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6614 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 42 473 505 473 473 473), lower := (rows 97 7 133 42 16 32 64 128 256), losses := [] }

theorem u6614 : Upper (D 3) (R 3) [96,5,129,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6615 : PairBound 9 := { available := 378, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 137 378 378 378 506 378), lower := (rows 97 7 133 137 16 32 64 128 256), losses := [] }

theorem u6615 : Upper (D 3) (R 3) [96,5,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6615
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6616 : PairBound 9 := { available := 377, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 138 377 377 377 505 377), lower := (rows 97 7 133 138 16 32 64 128 256), losses := [] }

theorem u6616 : Upper (D 3) (R 3) [96,5,129,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6617 : PairBound 9 := { available := 347, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 168 347 379 347 475 347), lower := (rows 97 7 133 168 16 32 64 128 256), losses := [] }

theorem u6617 : Upper (D 3) (R 3) [96,5,129,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6618 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 265 250 250 250 250 506), lower := (rows 97 7 133 265 16 32 64 128 256), losses := [] }

theorem u6618 : Upper (D 3) (R 3) [96,5,129,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6619 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 266 249 249 249 249 505), lower := (rows 97 7 133 266 16 32 64 128 256), losses := [] }

theorem u6619 : Upper (D 3) (R 3) [96,5,129,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6619
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6620 : PairBound 9 := { available := 219, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 296 219 251 219 219 475), lower := (rows 97 7 133 296 16 32 64 128 256), losses := [] }

theorem u6620 : Upper (D 3) (R 3) [96,5,129,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6620
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6621 : PairBound 9 := { available := 123, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 133 392 123 123 123 251 379), lower := (rows 97 7 133 392 16 32 64 128 256), losses := [] }

theorem u6621 : Upper (D 3) (R 3) [96,5,129,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6621
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6622_9 : Upper (D 3) (R 3) [96,5,130,17,9] 13 :=
  permutation_upper _ _ _ [96,5,3,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4010

theorem m6622_33 : Upper (D 3) (R 3) [96,5,130,17,33] 13 :=
  permutation_upper _ _ _ [96,5,33,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4170

theorem m6622_40 : Upper (D 3) (R 3) [96,5,130,17,40] 13 :=
  permutation_upper _ _ _ [96,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4210

theorem m6622_96 : Upper (D 3) (R 3) [96,5,130,17,96] 13 :=
  permutation_upper _ _ _ [96,5,96,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4281

theorem m6622_129 : Upper (D 3) (R 3) [96,5,130,17,129] 13 :=
  permutation_upper _ _ _ [96,5,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4302

def r6622 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6622 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u6622 : Upper (D 3) (R 3) [96,5,130,17] 13 := by
  apply FastRouting.sound _ _ [96,5,130,17] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r6622 c6622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6622_9
  · exact m6622_33
  · exact m6622_40
  · exact m6622_96
  · exact m6622_129
  · exact u4342
  · exact u4343
  · exact u4344
  · exact u4345
  · exact u4346
  · exact u4347

def b6623 : PairBound 9 := { available := 473, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 41 473 505 473 473 473), lower := (rows 97 7 134 41 16 32 64 128 256), losses := [] }

theorem u6623 : Upper (D 3) (R 3) [96,5,130,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6623
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6624_9 : Upper (D 3) (R 3) [96,5,130,48,9] 13 :=
  permutation_upper _ _ _ [96,5,34,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4210

theorem m6624_65 : Upper (D 3) (R 3) [96,5,130,48,65] 13 :=
  permutation_upper _ _ _ [96,5,130,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4348

def r6624 : Route 9 := (fun mask => (mask,id))

def c6624 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6624 : Upper (D 3) (R 3) [96,5,130,48] 13 := by
  apply FastRouting.sound _ _ [96,5,130,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6624 c6624
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6624_9
  · exact m6624_65
  · exact u4352
  · exact u4353
  · exact u4354
  · exact u4355
  · exact u4356
  · exact u4357
  · exact u4358
  · exact u4359

def b6625 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 134 104 409 441 473 409 409), lower := (rows 97 7 134 104 16 32 64 128 256), losses := [] }

theorem u6625 : Upper (D 3) (R 3) [96,5,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6626 : PairBound 9 := { available := 377, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 134 137 377 377 377 505 377), lower := (rows 97 7 134 137 16 32 64 128 256), losses := [] }

theorem u6626 : Upper (D 3) (R 3) [96,5,130,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6627 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 152 377 361 361 489 361), lower := (rows 97 7 134 152 16 32 64 128 256), losses := [] }

theorem u6627 : Upper (D 3) (R 3) [96,5,130,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6628 : PairBound 9 := { available := 345, camps := [{ cop := 3, region := 337, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 168 345 377 345 473 345), lower := (rows 97 7 134 168 16 32 64 128 256), losses := [] }

theorem u6628 : Upper (D 3) (R 3) [96,5,130,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6628
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6629_9 : Upper (D 3) (R 3) [96,5,130,257,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4344

theorem m6629_33 : Upper (D 3) (R 3) [96,5,130,257,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4349

theorem m6629_40 : Upper (D 3) (R 3) [96,5,130,257,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4356

theorem m6629_96 : Upper (D 3) (R 3) [96,5,130,257,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4360

theorem m6629_129 : Upper (D 3) (R 3) [96,5,130,257,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4362

theorem m6629_136 : Upper (D 3) (R 3) [96,5,130,257,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4365

theorem m6629_160 : Upper (D 3) (R 3) [96,5,130,257,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4368

def r6629 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6629 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6629 : Upper (D 3) (R 3) [96,5,130,257] 13 := by
  apply FastRouting.sound _ _ [96,5,130,257] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r6629 c6629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6629_9
  · exact m6629_33
  · exact m6629_40
  · exact m6629_96
  · exact m6629_129
  · exact m6629_136
  · exact m6629_160

theorem m6630_9 : Upper (D 3) (R 3) [96,5,130,272,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4345

theorem m6630_33 : Upper (D 3) (R 3) [96,5,130,272,33] 13 :=
  permutation_upper _ _ _ [96,5,130,33,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4350

theorem m6630_40 : Upper (D 3) (R 3) [96,5,130,272,40] 13 :=
  permutation_upper _ _ _ [96,5,130,48,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4357

theorem m6630_96 : Upper (D 3) (R 3) [96,5,130,272,96] 13 :=
  permutation_upper _ _ _ [96,5,130,96,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4361

theorem m6630_129 : Upper (D 3) (R 3) [96,5,130,272,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4363

theorem m6630_136 : Upper (D 3) (R 3) [96,5,130,272,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4366

theorem m6630_160 : Upper (D 3) (R 3) [96,5,130,272,160] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4369

def r6630 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6630 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6630 : Upper (D 3) (R 3) [96,5,130,272] 13 := by
  apply FastRouting.sound _ _ [96,5,130,272] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r6630 c6630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6630_9
  · exact m6630_33
  · exact m6630_40
  · exact m6630_96
  · exact m6630_129
  · exact m6630_136
  · exact m6630_160

theorem m6631_9 : Upper (D 3) (R 3) [96,5,130,288,9] 13 :=
  permutation_upper _ _ _ [96,5,130,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4346

theorem m6631_65 : Upper (D 3) (R 3) [96,5,130,288,65] 13 :=
  permutation_upper _ _ _ [96,5,130,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4351

theorem m6631_72 : Upper (D 3) (R 3) [96,5,130,288,72] 13 :=
  permutation_upper _ _ _ [96,5,130,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4358

theorem m6631_129 : Upper (D 3) (R 3) [96,5,130,288,129] 13 :=
  permutation_upper _ _ _ [96,5,130,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4364

theorem m6631_136 : Upper (D 3) (R 3) [96,5,130,288,136] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4367

theorem m6631_192 : Upper (D 3) (R 3) [96,5,130,288,192] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4370

def r6631 : Route 9 := (fun mask => (mask,id))

def c6631 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6631 : Upper (D 3) (R 3) [96,5,130,288] 13 := by
  apply FastRouting.sound _ _ [96,5,130,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6631 c6631
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6631_9
  · exact m6631_65
  · exact m6631_72
  · exact m6631_129
  · exact m6631_136
  · exact m6631_192

def b6632 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 392 121 121 121 249 377), lower := (rows 97 7 134 392 16 32 64 128 256), losses := [] }

theorem u6632 : Upper (D 3) (R 3) [96,5,130,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6632
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6633_3 : Upper (D 3) (R 3) [96,5,136,17,3] 13 :=
  permutation_upper _ _ _ [96,5,9,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4030

theorem m6633_33 : Upper (D 3) (R 3) [96,5,136,17,33] 13 :=
  permutation_upper _ _ _ [96,5,33,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4169

theorem m6633_34 : Upper (D 3) (R 3) [96,5,136,17,34] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4227

theorem m6633_96 : Upper (D 3) (R 3) [96,5,136,17,96] 13 :=
  permutation_upper _ _ _ [96,5,96,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4280

theorem m6633_129 : Upper (D 3) (R 3) [96,5,136,17,129] 13 :=
  permutation_upper _ _ _ [96,5,129,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4301

def r6633 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6633 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6633 : Upper (D 3) (R 3) [96,5,136,17] 13 := by
  apply FastRouting.sound _ _ [96,5,136,17] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r6633 c6633
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6633_3
  · exact m6633_33
  · exact m6633_34
  · exact m6633_96
  · exact m6633_129
  · exact u4371
  · exact u4372
  · exact u4373
  · exact u4374
  · exact u4375
  · exact u4376

def r6634 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6634 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6634 : Upper (D 3) (R 3) [96,5,136,18] 13 := by
  apply FastRouting.sound _ _ [96,5,136,18] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r6634 c6634
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u4377
  · exact u4378
  · exact u4379
  · exact u4380
  · exact u4381
  · exact u4382
  · exact u4383

def b6635 : PairBound 9 := { available := 467, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 41 467 499 467 467 467), lower := (rows 97 7 140 41 16 32 64 128 256), losses := [] }

theorem u6635 : Upper (D 3) (R 3) [96,5,136,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6636 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 400, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 42 465 497 465 465 465), lower := (rows 97 7 140 42 16 32 64 128 256), losses := [] }

theorem u6636 : Upper (D 3) (R 3) [96,5,136,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6637 : PairBound 9 := { available := 451, camps := [{ cop := 1, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 56 467 483 451 451 451), lower := (rows 97 7 140 56 16 32 64 128 256), losses := [] }

theorem u6637 : Upper (D 3) (R 3) [96,5,136,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6638 : PairBound 9 := { available := 403, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 7 140 104 403 435 467 403 403), lower := (rows 97 7 140 104 16 32 64 128 256), losses := [] }

theorem u6638 : Upper (D 3) (R 3) [96,5,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6639 : PairBound 9 := { available := 371, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 97 7 140 137 371 371 371 499 371), lower := (rows 97 7 140 137 16 32 64 128 256), losses := [] }

theorem u6639 : Upper (D 3) (R 3) [96,5,136,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6639
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6640 : PairBound 9 := { available := 369, camps := [{ cop := 2, region := 369, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 138 369 369 369 497 369), lower := (rows 97 7 140 138 16 32 64 128 256), losses := [] }

theorem u6640 : Upper (D 3) (R 3) [96,5,136,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6640
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6641 : PairBound 9 := { available := 355, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 152 371 355 355 483 355), lower := (rows 97 7 140 152 16 32 64 128 256), losses := [] }

theorem u6641 : Upper (D 3) (R 3) [96,5,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6642 : PairBound 9 := { available := 339, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 168 339 371 339 467 339), lower := (rows 97 7 140 168 16 32 64 128 256), losses := [] }

theorem u6642 : Upper (D 3) (R 3) [96,5,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6642
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6643_3 : Upper (D 3) (R 3) [96,5,136,257,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4063

def r6643 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6643 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6643 : Upper (D 3) (R 3) [96,5,136,257] 13 := by
  apply FastRouting.sound _ _ [96,5,136,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6643 c6643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6643_3
  · exact u4422
  · exact u4423
  · exact u4424
  · exact u4425
  · exact u4426
  · exact u4427

def r6644 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6644 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6644 : Upper (D 3) (R 3) [96,5,136,258] 13 := by
  apply FastRouting.sound _ _ [96,5,136,258] 13 (by decide) (choices 2) [33,96,129,160] r6644 c6644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u4428
  · exact u4429
  · exact u4430
  · exact u4431

theorem m6645_3 : Upper (D 3) (R 3) [96,5,136,272,3] 13 :=
  permutation_upper _ _ _ [96,5,9,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4064

def r6645 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6645 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6645 : Upper (D 3) (R 3) [96,5,136,272] 13 := by
  apply FastRouting.sound _ _ [96,5,136,272] 13 (by decide) (choices 2) [3,33,34,96,129,130,160] r6645 c6645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6645_3
  · exact u4432
  · exact u4433
  · exact u4434
  · exact u4435
  · exact u4436
  · exact u4437

def b6646 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 97 7 140 296 211 243 211 211 467), lower := (rows 97 7 140 296 16 32 64 128 256), losses := [] }

theorem u6646 : Upper (D 3) (R 3) [96,5,136,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6646
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6647 : PairBound 9 := { available := 115, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 392 115 115 115 243 371), lower := (rows 97 7 140 392 16 32 64 128 256), losses := [] }

theorem u6647 : Upper (D 3) (R 3) [96,5,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6647
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6648_9 : Upper (D 3) (R 3) [96,5,144,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4227

theorem m6648_65 : Upper (D 3) (R 3) [96,5,144,34,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4384

theorem m6648_72 : Upper (D 3) (R 3) [96,5,144,34,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4396

theorem m6648_129 : Upper (D 3) (R 3) [96,5,144,34,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4408

theorem m6648_136 : Upper (D 3) (R 3) [96,5,144,34,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4414

theorem m6648_192 : Upper (D 3) (R 3) [96,5,144,34,192] 13 :=
  permutation_upper _ _ _ [96,5,136,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4418

theorem m6648_257 : Upper (D 3) (R 3) [96,5,144,34,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4423

theorem m6648_264 : Upper (D 3) (R 3) [96,5,144,34,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4433

theorem m6648_320 : Upper (D 3) (R 3) [96,5,144,34,320] 13 :=
  permutation_upper _ _ _ [96,5,136,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4438

theorem m6648_384 : Upper (D 3) (R 3) [96,5,144,34,384] 13 :=
  permutation_upper _ _ _ [96,5,136,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4442

def r6648 : Route 9 := (fun mask => (mask,id))

def c6648 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6648 : Upper (D 3) (R 3) [96,5,144,34] 13 := by
  apply FastRouting.sound _ _ [96,5,144,34] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6648 c6648
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6648_9
  · exact m6648_65
  · exact m6648_72
  · exact m6648_129
  · exact m6648_136
  · exact m6648_192
  · exact m6648_257
  · exact m6648_264
  · exact m6648_320
  · exact m6648_384

theorem m6649_3 : Upper (D 3) (R 3) [96,5,144,129,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4057

theorem m6649_9 : Upper (D 3) (R 3) [96,5,144,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4301

theorem m6649_10 : Upper (D 3) (R 3) [96,5,144,129,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4379

theorem m6649_33 : Upper (D 3) (R 3) [96,5,144,129,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4385

theorem m6649_34 : Upper (D 3) (R 3) [96,5,144,129,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4391

theorem m6649_40 : Upper (D 3) (R 3) [96,5,144,129,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4397

theorem m6649_96 : Upper (D 3) (R 3) [96,5,144,129,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4404

theorem m6649_257 : Upper (D 3) (R 3) [96,5,144,129,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4425

theorem m6649_258 : Upper (D 3) (R 3) [96,5,144,129,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4430

theorem m6649_264 : Upper (D 3) (R 3) [96,5,144,129,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4435

theorem m6649_288 : Upper (D 3) (R 3) [96,5,144,129,288] 13 :=
  permutation_upper _ _ _ [96,5,136,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4439

def r6649 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6649 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6649 : Upper (D 3) (R 3) [96,5,144,129] 13 := by
  apply FastRouting.sound _ _ [96,5,144,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r6649 c6649
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6649_3
  · exact m6649_9
  · exact m6649_10
  · exact m6649_33
  · exact m6649_34
  · exact m6649_40
  · exact m6649_96
  · exact m6649_257
  · exact m6649_258
  · exact m6649_264
  · exact m6649_288

def b6650 : PairBound 9 := { available := 361, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 148 138 377 361 361 489 361), lower := (rows 97 7 148 138 16 32 64 128 256), losses := [] }

theorem u6650 : Upper (D 3) (R 3) [96,5,144,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6650
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6651_3 : Upper (D 3) (R 3) [96,5,144,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4058

theorem m6651_9 : Upper (D 3) (R 3) [96,5,144,160,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4372

theorem m6651_10 : Upper (D 3) (R 3) [96,5,144,160,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4380

theorem m6651_65 : Upper (D 3) (R 3) [96,5,144,160,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4386

theorem m6651_66 : Upper (D 3) (R 3) [96,5,144,160,66] 13 :=
  permutation_upper _ _ _ [96,5,136,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4392

theorem m6651_72 : Upper (D 3) (R 3) [96,5,144,160,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4399

theorem m6651_257 : Upper (D 3) (R 3) [96,5,144,160,257] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4427

theorem m6651_258 : Upper (D 3) (R 3) [96,5,144,160,258] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4431

theorem m6651_264 : Upper (D 3) (R 3) [96,5,144,160,264] 13 :=
  permutation_upper _ _ _ [96,5,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4437

theorem m6651_320 : Upper (D 3) (R 3) [96,5,144,160,320] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4441

def r6651 : Route 9 := (fun mask => (mask,id))

def c6651 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6651 : Upper (D 3) (R 3) [96,5,144,160] 13 := by
  apply FastRouting.sound _ _ [96,5,144,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r6651 c6651
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6651_3
  · exact m6651_9
  · exact m6651_10
  · exact m6651_65
  · exact m6651_66
  · exact m6651_72
  · exact m6651_257
  · exact m6651_258
  · exact m6651_264
  · exact m6651_320

theorem m6652_3 : Upper (D 3) (R 3) [96,5,144,257,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4059

theorem m6652_9 : Upper (D 3) (R 3) [96,5,144,257,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4373

theorem m6652_10 : Upper (D 3) (R 3) [96,5,144,257,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4381

theorem m6652_33 : Upper (D 3) (R 3) [96,5,144,257,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4387

theorem m6652_34 : Upper (D 3) (R 3) [96,5,144,257,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4393

theorem m6652_40 : Upper (D 3) (R 3) [96,5,144,257,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4400

theorem m6652_96 : Upper (D 3) (R 3) [96,5,144,257,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4405

theorem m6652_129 : Upper (D 3) (R 3) [96,5,144,257,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4409

theorem m6652_130 : Upper (D 3) (R 3) [96,5,144,257,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4412

theorem m6652_136 : Upper (D 3) (R 3) [96,5,144,257,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4415

theorem m6652_160 : Upper (D 3) (R 3) [96,5,144,257,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4419

def r6652 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6652 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6652 : Upper (D 3) (R 3) [96,5,144,257] 13 := by
  apply FastRouting.sound _ _ [96,5,144,257] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,129,130,136,160] r6652 c6652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6652_3
  · exact m6652_9
  · exact m6652_10
  · exact m6652_33
  · exact m6652_34
  · exact m6652_40
  · exact m6652_96
  · exact m6652_129
  · exact m6652_130
  · exact m6652_136
  · exact m6652_160

theorem m6653_9 : Upper (D 3) (R 3) [96,5,144,258,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4374

theorem m6653_33 : Upper (D 3) (R 3) [96,5,144,258,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4388

theorem m6653_40 : Upper (D 3) (R 3) [96,5,144,258,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4401

theorem m6653_96 : Upper (D 3) (R 3) [96,5,144,258,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4406

theorem m6653_129 : Upper (D 3) (R 3) [96,5,144,258,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4410

theorem m6653_136 : Upper (D 3) (R 3) [96,5,144,258,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4416

theorem m6653_160 : Upper (D 3) (R 3) [96,5,144,258,160] 13 :=
  permutation_upper _ _ _ [96,5,136,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4420

def r6653 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6653 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6653 : Upper (D 3) (R 3) [96,5,144,258] 13 := by
  apply FastRouting.sound _ _ [96,5,144,258] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r6653 c6653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6653_9
  · exact m6653_33
  · exact m6653_40
  · exact m6653_96
  · exact m6653_129
  · exact m6653_136
  · exact m6653_160

theorem m6654_3 : Upper (D 3) (R 3) [96,5,144,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4060

theorem m6654_9 : Upper (D 3) (R 3) [96,5,144,288,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4375

theorem m6654_10 : Upper (D 3) (R 3) [96,5,144,288,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4382

theorem m6654_65 : Upper (D 3) (R 3) [96,5,144,288,65] 13 :=
  permutation_upper _ _ _ [96,5,136,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4389

theorem m6654_66 : Upper (D 3) (R 3) [96,5,144,288,66] 13 :=
  permutation_upper _ _ _ [96,5,136,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4394

theorem m6654_72 : Upper (D 3) (R 3) [96,5,144,288,72] 13 :=
  permutation_upper _ _ _ [96,5,136,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4402

theorem m6654_129 : Upper (D 3) (R 3) [96,5,144,288,129] 13 :=
  permutation_upper _ _ _ [96,5,136,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4411

theorem m6654_130 : Upper (D 3) (R 3) [96,5,144,288,130] 13 :=
  permutation_upper _ _ _ [96,5,136,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4413

theorem m6654_136 : Upper (D 3) (R 3) [96,5,144,288,136] 13 :=
  permutation_upper _ _ _ [96,5,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4417

theorem m6654_192 : Upper (D 3) (R 3) [96,5,144,288,192] 13 :=
  permutation_upper _ _ _ [96,5,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4421

def r6654 : Route 9 := (fun mask => (mask,id))

def c6654 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6654 : Upper (D 3) (R 3) [96,5,144,288] 13 := by
  apply FastRouting.sound _ _ [96,5,144,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r6654 c6654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6654_3
  · exact m6654_9
  · exact m6654_10
  · exact m6654_65
  · exact m6654_66
  · exact m6654_72
  · exact m6654_129
  · exact m6654_130
  · exact m6654_136
  · exact m6654_192

theorem m6655_3 : Upper (D 3) (R 3) [96,5,144,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,130,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4061

theorem m6655_9 : Upper (D 3) (R 3) [96,5,144,384,9] 13 :=
  permutation_upper _ _ _ [96,5,136,17,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4376

theorem m6655_10 : Upper (D 3) (R 3) [96,5,144,384,10] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4383

theorem m6655_33 : Upper (D 3) (R 3) [96,5,144,384,33] 13 :=
  permutation_upper _ _ _ [96,5,136,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4390

theorem m6655_34 : Upper (D 3) (R 3) [96,5,144,384,34] 13 :=
  permutation_upper _ _ _ [96,5,136,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4395

theorem m6655_40 : Upper (D 3) (R 3) [96,5,144,384,40] 13 :=
  permutation_upper _ _ _ [96,5,136,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4403

theorem m6655_96 : Upper (D 3) (R 3) [96,5,144,384,96] 13 :=
  permutation_upper _ _ _ [96,5,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u4407

def r6655 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c6655 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6655 : Upper (D 3) (R 3) [96,5,144,384] 13 := by
  apply FastRouting.sound _ _ [96,5,144,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,96] r6655 c6655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6655_3
  · exact m6655_9
  · exact m6655_10
  · exact m6655_33
  · exact m6655_34
  · exact m6655_40
  · exact m6655_96

def b6656 : PairBound 9 := { available := 457, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 26 473 489 457 457 457), lower := (rows 97 7 164 26 16 32 64 128 256), losses := [] }

theorem u6656 : Upper (D 3) (R 3) [96,5,160,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6657 : PairBound 9 := { available := 409, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 74 409 441 473 409 409), lower := (rows 97 7 164 74 16 32 64 128 256), losses := [] }

theorem u6657 : Upper (D 3) (R 3) [96,5,160,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6657
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6658 : PairBound 9 := { available := 347, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 137 347 379 347 475 347), lower := (rows 97 7 164 137 16 32 64 128 256), losses := [] }

theorem u6658 : Upper (D 3) (R 3) [96,5,160,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6659 : PairBound 9 := { available := 345, camps := [{ cop := 1, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 97 7 164 138 345 377 345 473 345), lower := (rows 97 7 164 138 16 32 64 128 256), losses := [] }

theorem u6659 : Upper (D 3) (R 3) [96,5,160,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6659
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u6659
end Delivery.IrregularNine14.P03
