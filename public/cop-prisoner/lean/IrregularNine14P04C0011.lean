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

def b660 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 137 281 313 345 409 281), lower := (rows 7 38 70 137 16 32 64 128 256), losses := [] }

theorem u660 : Upper (D 4) (R 4) [6,36,66,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b660
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b661 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 408, targets := 2 }], pairs := [(3,1)], upper := (rows 7 38 70 392 25 57 89 153 281), lower := (rows 7 38 70 392 16 32 64 128 256), losses := [] }

theorem u661 : Upper (D 4) (R 4) [6,36,66,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b661
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b662 : PairBound 9 := { available := 411, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 25 411 443 475 411 411), lower := (rows 7 38 76 25 16 32 64 128 256), losses := [] }

theorem u662 : Upper (D 4) (R 4) [6,36,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b662
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b663 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 137 283 315 347 411 283), lower := (rows 7 38 76 137 16 32 64 128 256), losses := [] }

theorem u663 : Upper (D 4) (R 4) [6,36,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b663
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b664 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 138 281 313 345 409 281), lower := (rows 7 38 76 138 16 32 64 128 256), losses := [] }

theorem u664 : Upper (D 4) (R 4) [6,36,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b664
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b665 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 76 392 27 59 91 155 283), lower := (rows 7 38 76 392 16 32 64 128 256), losses := [] }

theorem u665 : Upper (D 4) (R 4) [6,36,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b665
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b666 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 84 137 283 315 347 411 283), lower := (rows 7 38 84 137 16 32 64 128 256), losses := [] }

theorem u666 : Upper (D 4) (R 4) [6,36,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b666
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b667 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 408, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 84 392 27 59 91 155 283), lower := (rows 7 38 84 392 16 32 64 128 256), losses := [] }

theorem u667 : Upper (D 4) (R 4) [6,36,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b667
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b668 : PairBound 9 := { available := 283, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 196 25 283 315 347 411 283), lower := (rows 7 38 196 25 16 32 64 128 256), losses := [] }

theorem u668 : Upper (D 4) (R 4) [6,36,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b668
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b669 : PairBound 9 := { available := 27, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 196 265 27 59 91 155 283), lower := (rows 7 38 196 265 16 32 64 128 256), losses := [] }

theorem u669 : Upper (D 4) (R 4) [6,36,192,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b669
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b670 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 280, targets := 4 }], pairs := [(3,2)], upper := (rows 7 38 196 266 25 57 89 153 281), lower := (rows 7 38 196 266 16 32 64 128 256), losses := [] }

theorem u670 : Upper (D 4) (R 4) [6,36,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b670
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b671 : PairBound 9 := { available := 279, camps := [{ cop := 0, region := 272, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 137 279 311 343 407 279), lower := (rows 7 42 76 137 16 32 64 128 256), losses := [] }

theorem u671 : Upper (D 4) (R 4) [6,40,72,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b671
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b672 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 272, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 76 138 277 309 341 405 277), lower := (rows 7 42 76 138 16 32 64 128 256), losses := [] }

theorem u672 : Upper (D 4) (R 4) [6,40,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b672
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b673 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 16, targets := 8 }], pairs := [(4,3)], upper := (rows 7 42 76 392 23 55 87 151 279), lower := (rows 7 42 76 392 16 32 64 128 256), losses := [] }

theorem u673 : Upper (D 4) (R 4) [6,40,72,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b673
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m674_3 : Upper (D 4) (R 4) [6,40,80,17,3] 13 :=
  permutation_upper _ _ _ [6,12,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u334

theorem m674_5 : Upper (D 4) (R 4) [6,40,80,17,5] 13 :=
  permutation_upper _ _ _ [6,12,24,34,65] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u336

theorem m674_6 : Upper (D 4) (R 4) [6,40,80,17,6] 13 :=
  permutation_upper _ _ _ [6,24,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u400

theorem m674_9 : Upper (D 4) (R 4) [6,40,80,17,9] 13 :=
  permutation_upper _ _ _ [6,5,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u223

theorem m674_10 : Upper (D 4) (R 4) [6,40,80,17,10] 13 :=
  permutation_upper _ _ _ [6,9,24,33,66] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u265

theorem m674_12 : Upper (D 4) (R 4) [6,40,80,17,12] 13 :=
  permutation_upper _ _ _ [6,9,24,34,65] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u268

theorem m674_129 : Upper (D 4) (R 4) [6,40,80,17,129] 13 :=
  permutation_upper _ _ _ [6,24,34,65,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u415

theorem m674_130 : Upper (D 4) (R 4) [6,40,80,17,130] 13 :=
  permutation_upper _ _ _ [6,24,40,65,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u419

theorem m674_132 : Upper (D 4) (R 4) [6,40,80,17,132] 13 :=
  permutation_upper _ _ _ [6,24,40,68,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u424

theorem m674_136 : Upper (D 4) (R 4) [6,40,80,17,136] 13 :=
  permutation_upper _ _ _ [6,24,33,65,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u405

theorem m674_384 : Upper (D 4) (R 4) [6,40,80,17,384] 13 :=
  permutation_upper _ _ _ [6,24,96,129,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u435

def r674 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c674 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u674 : Upper (D 4) (R 4) [6,40,80,17] 13 := by
  apply FastRouting.sound _ _ [6,40,80,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,384] r674 c674
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m674_3
  · exact m674_5
  · exact m674_6
  · exact m674_9
  · exact m674_10
  · exact m674_12
  · exact m674_129
  · exact m674_130
  · exact m674_132
  · exact m674_136
  · exact m674_384

theorem m675_5 : Upper (D 4) (R 4) [6,40,80,18,5] 13 :=
  permutation_upper _ _ _ [6,12,33,80,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u345

theorem m675_9 : Upper (D 4) (R 4) [6,40,80,18,9] 13 :=
  permutation_upper _ _ _ [6,9,24,34,65] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u268

theorem m675_12 : Upper (D 4) (R 4) [6,40,80,18,12] 13 :=
  permutation_upper _ _ _ [6,9,33,66,12] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u281

theorem m675_129 : Upper (D 4) (R 4) [6,40,80,18,129] 13 :=
  permutation_upper _ _ _ [6,33,72,18,132] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u455

theorem m675_132 : Upper (D 4) (R 4) [6,40,80,18,132] 13 :=
  permutation_upper _ _ _ [6,33,72,132,10] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u470

theorem m675_136 : Upper (D 4) (R 4) [6,40,80,18,136] 13 :=
  permutation_upper _ _ _ [6,33,65,18,132] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u441

theorem m675_384 : Upper (D 4) (R 4) [6,40,80,18,384] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u485

def r675 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c675 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u675 : Upper (D 4) (R 4) [6,40,80,18] 13 := by
  apply FastRouting.sound _ _ [6,40,80,18] 13 (by decide) (choices 2) [5,9,12,129,132,136,384] r675 c675
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m675_5
  · exact m675_9
  · exact m675_12
  · exact m675_129
  · exact m675_132
  · exact m675_136
  · exact m675_384

def b676 : PairBound 9 := { available := 395, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 42 84 28 411 427 459 395 395), lower := (rows 7 42 84 28 16 32 64 128 256), losses := [] }

theorem u676 : Upper (D 4) (R 4) [6,40,80,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b676
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m677_3 : Upper (D 4) (R 4) [6,40,80,129,3] 13 :=
  permutation_upper _ _ _ [6,12,48,65,130] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u372

theorem m677_5 : Upper (D 4) (R 4) [6,40,80,129,5] 13 :=
  permutation_upper _ _ _ [6,12,33,80,130] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u347

theorem m677_6 : Upper (D 4) (R 4) [6,40,80,129,6] 13 :=
  permutation_upper _ _ _ [6,33,72,144,6] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u474

theorem m677_9 : Upper (D 4) (R 4) [6,40,80,129,9] 13 :=
  permutation_upper _ _ _ [6,24,34,65,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u415

theorem m677_10 : Upper (D 4) (R 4) [6,40,80,129,10] 13 :=
  permutation_upper _ _ _ [6,36,72,18,129] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u491

theorem m677_12 : Upper (D 4) (R 4) [6,40,80,129,12] 13 :=
  permutation_upper _ _ _ [6,33,72,18,132] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u455

def r677 : Route 9 := (fun mask => (mask,id))

def c677 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u677 : Upper (D 4) (R 4) [6,40,80,129] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r677 c677
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m677_3
  · exact m677_5
  · exact m677_6
  · exact m677_9
  · exact m677_10
  · exact m677_12
  · exact u508
  · exact u509
  · exact u510
  · exact u511

theorem m678_5 : Upper (D 4) (R 4) [6,40,80,130,5] 13 :=
  permutation_upper _ _ _ [6,12,33,80,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u348

theorem m678_9 : Upper (D 4) (R 4) [6,40,80,130,9] 13 :=
  permutation_upper _ _ _ [6,24,40,68,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u424

theorem m678_12 : Upper (D 4) (R 4) [6,40,80,130,12] 13 :=
  permutation_upper _ _ _ [6,33,72,132,10] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u470

theorem m678_257 : Upper (D 4) (R 4) [6,40,80,130,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,260] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u510

def r678 : Route 9 := (fun mask => (mask,id))

def c678 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u678 : Upper (D 4) (R 4) [6,40,80,130] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r678 c678
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m678_5
  · exact m678_9
  · exact m678_12
  · exact m678_257
  · exact u512
  · exact u513

theorem m679_3 : Upper (D 4) (R 4) [6,40,80,132,3] 13 :=
  permutation_upper _ _ _ [6,12,48,65,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u373

theorem m679_9 : Upper (D 4) (R 4) [6,40,80,132,9] 13 :=
  permutation_upper _ _ _ [6,24,40,65,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u419

theorem m679_10 : Upper (D 4) (R 4) [6,40,80,132,10] 13 :=
  permutation_upper _ _ _ [6,36,72,129,10] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u493

theorem m679_257 : Upper (D 4) (R 4) [6,40,80,132,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,258] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u509

def r679 : Route 9 := (fun mask => (mask,id))

def c679 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u679 : Upper (D 4) (R 4) [6,40,80,132] 13 := by
  apply FastRouting.sound _ _ [6,40,80,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r679 c679
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m679_3
  · exact m679_9
  · exact m679_10
  · exact m679_257
  · exact u514
  · exact u515

theorem m680_3 : Upper (D 4) (R 4) [6,40,80,144,3] 13 :=
  permutation_upper _ _ _ [6,12,48,65,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u371

theorem m680_5 : Upper (D 4) (R 4) [6,40,80,144,5] 13 :=
  permutation_upper _ _ _ [6,12,33,80,129] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u346

theorem m680_6 : Upper (D 4) (R 4) [6,40,80,144,6] 13 :=
  permutation_upper _ _ _ [6,33,72,129,6] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u460

theorem m680_9 : Upper (D 4) (R 4) [6,40,80,144,9] 13 :=
  permutation_upper _ _ _ [6,24,33,65,132] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 6 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u405

theorem m680_10 : Upper (D 4) (R 4) [6,40,80,144,10] 13 :=
  permutation_upper _ _ _ [6,33,66,20,129] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u446

theorem m680_12 : Upper (D 4) (R 4) [6,40,80,144,12] 13 :=
  permutation_upper _ _ _ [6,33,65,18,132] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u441

theorem m680_257 : Upper (D 4) (R 4) [6,40,80,144,257] 13 :=
  permutation_upper _ _ _ [6,40,80,129,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u511

theorem m680_258 : Upper (D 4) (R 4) [6,40,80,144,258] 13 :=
  permutation_upper _ _ _ [6,40,80,132,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u515

theorem m680_260 : Upper (D 4) (R 4) [6,40,80,144,260] 13 :=
  permutation_upper _ _ _ [6,40,80,130,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u513

def r680 : Route 9 := (fun mask => (mask,id))

def c680 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u680 : Upper (D 4) (R 4) [6,40,80,144] 13 := by
  apply FastRouting.sound _ _ [6,40,80,144] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r680 c680
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m680_3
  · exact m680_5
  · exact m680_6
  · exact m680_9
  · exact m680_10
  · exact m680_12
  · exact m680_257
  · exact m680_258
  · exact m680_260
  · exact u516

theorem m681_3 : Upper (D 4) (R 4) [6,40,80,384,3] 13 :=
  permutation_upper _ _ _ [6,12,48,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u374

theorem m681_5 : Upper (D 4) (R 4) [6,40,80,384,5] 13 :=
  permutation_upper _ _ _ [6,12,33,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u349

theorem m681_6 : Upper (D 4) (R 4) [6,40,80,384,6] 13 :=
  permutation_upper _ _ _ [6,33,72,384,6] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u479

theorem m681_9 : Upper (D 4) (R 4) [6,40,80,384,9] 13 :=
  permutation_upper _ _ _ [6,24,96,129,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 6 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 7 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u435

theorem m681_10 : Upper (D 4) (R 4) [6,40,80,384,10] 13 :=
  permutation_upper _ _ _ [6,36,192,18,257] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u502

theorem m681_12 : Upper (D 4) (R 4) [6,40,80,384,12] 13 :=
  permutation_upper _ _ _ [6,33,192,18,260] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u485

def r681 : Route 9 := (fun mask => (mask,id))

def c681 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u681 : Upper (D 4) (R 4) [6,40,80,384] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r681 c681
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m681_3
  · exact m681_5
  · exact m681_6
  · exact m681_9
  · exact m681_10
  · exact m681_12

theorem m682_3 : Upper (D 4) (R 4) [6,40,192,17,3] 13 :=
  permutation_upper _ _ _ [6,12,24,33,192] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u335

theorem m682_5 : Upper (D 4) (R 4) [6,40,192,17,5] 13 :=
  permutation_upper _ _ _ [6,12,24,96,129] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u337

theorem m682_6 : Upper (D 4) (R 4) [6,40,192,17,6] 13 :=
  permutation_upper _ _ _ [6,24,24,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u401

theorem m682_9 : Upper (D 4) (R 4) [6,40,192,17,9] 13 :=
  permutation_upper _ _ _ [6,5,24,33,192] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u224

theorem m682_10 : Upper (D 4) (R 4) [6,40,192,17,10] 13 :=
  permutation_upper _ _ _ [6,9,24,33,192] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u267

theorem m682_12 : Upper (D 4) (R 4) [6,40,192,17,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,129] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u277

theorem m682_257 : Upper (D 4) (R 4) [6,40,192,17,257] 13 :=
  permutation_upper _ _ _ [6,24,34,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u416

theorem m682_258 : Upper (D 4) (R 4) [6,40,192,17,258] 13 :=
  permutation_upper _ _ _ [6,24,40,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u420

theorem m682_260 : Upper (D 4) (R 4) [6,40,192,17,260] 13 :=
  permutation_upper _ _ _ [6,24,40,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u430

theorem m682_264 : Upper (D 4) (R 4) [6,40,192,17,264] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u407

def r682 : Route 9 := (fun mask => (mask,id))

def c682 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u682 : Upper (D 4) (R 4) [6,40,192,17] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r682 c682
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m682_3
  · exact m682_5
  · exact m682_6
  · exact m682_9
  · exact m682_10
  · exact m682_12
  · exact m682_257
  · exact m682_258
  · exact m682_260
  · exact m682_264

theorem m683_5 : Upper (D 4) (R 4) [6,40,192,18,5] 13 :=
  permutation_upper _ _ _ [6,12,96,144,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u395

theorem m683_9 : Upper (D 4) (R 4) [6,40,192,18,9] 13 :=
  permutation_upper _ _ _ [6,9,24,34,192] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u270

theorem m683_12 : Upper (D 4) (R 4) [6,40,192,18,12] 13 :=
  permutation_upper _ _ _ [6,9,33,192,12] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u289

theorem m683_257 : Upper (D 4) (R 4) [6,40,192,18,257] 13 :=
  permutation_upper _ _ _ [6,33,72,18,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u457

theorem m683_260 : Upper (D 4) (R 4) [6,40,192,18,260] 13 :=
  permutation_upper _ _ _ [6,33,72,384,10] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u480

theorem m683_264 : Upper (D 4) (R 4) [6,40,192,18,264] 13 :=
  permutation_upper _ _ _ [6,33,65,18,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u443

def r683 : Route 9 := (fun mask => (mask,id))

def c683 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u683 : Upper (D 4) (R 4) [6,40,192,18] 13 := by
  apply FastRouting.sound _ _ [6,40,192,18] 13 (by decide) (choices 2) [5,9,12,257,260,264] r683 c683
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m683_5
  · exact m683_9
  · exact m683_12
  · exact m683_257
  · exact m683_260
  · exact m683_264

theorem m684_3 : Upper (D 4) (R 4) [6,40,192,20,3] 13 :=
  permutation_upper _ _ _ [6,12,48,192,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u383

theorem m684_9 : Upper (D 4) (R 4) [6,40,192,20,9] 13 :=
  permutation_upper _ _ _ [6,9,24,96,130] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u278

theorem m684_10 : Upper (D 4) (R 4) [6,40,192,20,10] 13 :=
  permutation_upper _ _ _ [6,9,34,192,12] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u300

theorem m684_264 : Upper (D 4) (R 4) [6,40,192,20,264] 13 :=
  permutation_upper _ _ _ [6,33,192,20,257] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u486

def r684 : Route 9 := (fun mask => (mask,id))

def c684 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u684 : Upper (D 4) (R 4) [6,40,192,20] 13 := by
  apply FastRouting.sound _ _ [6,40,192,20] 13 (by decide) (choices 2) [3,9,10,257,258,264] r684 c684
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m684_3
  · exact m684_9
  · exact m684_10
  · exact u517
  · exact u518
  · exact m684_264

theorem m685_3 : Upper (D 4) (R 4) [6,40,192,257,3] 13 :=
  permutation_upper _ _ _ [6,12,48,192,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u385

theorem m685_5 : Upper (D 4) (R 4) [6,40,192,257,5] 13 :=
  permutation_upper _ _ _ [6,12,96,144,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u397

theorem m685_9 : Upper (D 4) (R 4) [6,40,192,257,9] 13 :=
  permutation_upper _ _ _ [6,24,34,68,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u417

theorem m685_10 : Upper (D 4) (R 4) [6,40,192,257,10] 13 :=
  permutation_upper _ _ _ [6,36,72,18,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u492

theorem m685_12 : Upper (D 4) (R 4) [6,40,192,257,12] 13 :=
  permutation_upper _ _ _ [6,40,192,20,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u518

def r685 : Route 9 := (fun mask => (mask,id))

def c685 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u685 : Upper (D 4) (R 4) [6,40,192,257] 13 := by
  apply FastRouting.sound _ _ [6,40,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r685 c685
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m685_3
  · exact m685_5
  · exact u519
  · exact m685_9
  · exact m685_10
  · exact m685_12

theorem m686_5 : Upper (D 4) (R 4) [6,40,192,258,5] 13 :=
  permutation_upper _ _ _ [6,12,96,144,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u398

theorem m686_9 : Upper (D 4) (R 4) [6,40,192,258,9] 13 :=
  permutation_upper _ _ _ [6,24,40,68,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u426

def r686 : Route 9 := (fun mask => (mask,id))

def c686 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u686 : Upper (D 4) (R 4) [6,40,192,258] 13 := by
  apply FastRouting.sound _ _ [6,40,192,258] 13 (by decide) (choices 2) [5,9,12] r686 c686
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m686_5
  · exact m686_9
  · exact u520

theorem m687_3 : Upper (D 4) (R 4) [6,40,192,260,3] 13 :=
  permutation_upper _ _ _ [6,12,48,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u386

theorem m687_9 : Upper (D 4) (R 4) [6,40,192,260,9] 13 :=
  permutation_upper _ _ _ [6,24,40,192,260] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u432

theorem m687_10 : Upper (D 4) (R 4) [6,40,192,260,10] 13 :=
  permutation_upper _ _ _ [6,36,72,384,10] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u501

def r687 : Route 9 := (fun mask => (mask,id))

def c687 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u687 : Upper (D 4) (R 4) [6,40,192,260] 13 := by
  apply FastRouting.sound _ _ [6,40,192,260] 13 (by decide) (choices 2) [3,9,10] r687 c687
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m687_3
  · exact m687_9
  · exact m687_10

theorem m688_3 : Upper (D 4) (R 4) [6,40,192,272,3] 13 :=
  permutation_upper _ _ _ [6,12,48,192,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u384

theorem m688_5 : Upper (D 4) (R 4) [6,40,192,272,5] 13 :=
  permutation_upper _ _ _ [6,12,96,144,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u396

theorem m688_6 : Upper (D 4) (R 4) [6,40,192,272,6] 13 :=
  permutation_upper _ _ _ [6,40,192,257,6] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u519

theorem m688_9 : Upper (D 4) (R 4) [6,40,192,272,9] 13 :=
  permutation_upper _ _ _ [6,24,33,68,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u412

theorem m688_10 : Upper (D 4) (R 4) [6,40,192,272,10] 13 :=
  permutation_upper _ _ _ [6,33,66,20,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u448

theorem m688_12 : Upper (D 4) (R 4) [6,40,192,272,12] 13 :=
  permutation_upper _ _ _ [6,33,192,20,258] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u487

def r688 : Route 9 := (fun mask => (mask,id))

def c688 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u688 : Upper (D 4) (R 4) [6,40,192,272] 13 := by
  apply FastRouting.sound _ _ [6,40,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12] r688 c688
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m688_3
  · exact m688_5
  · exact m688_6
  · exact m688_9
  · exact m688_10
  · exact m688_12

def b689 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 7 50 84 137 287 303 335 399 271), lower := (rows 7 50 84 137 16 32 64 128 256), losses := [] }

theorem u689 : Upper (D 4) (R 4) [6,48,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b689
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b690 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 392, targets := 16 }], pairs := [(3,4)], upper := (rows 7 50 84 392 31 47 79 143 271), lower := (rows 7 50 84 392 16 32 64 128 256), losses := [] }

theorem u690 : Upper (D 4) (R 4) [6,48,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b690
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m691_3 : Upper (D 4) (R 4) [6,48,192,257,3] 13 :=
  permutation_upper _ _ _ [6,12,33,192,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u352

theorem m691_5 : Upper (D 4) (R 4) [6,48,192,257,5] 13 :=
  permutation_upper _ _ _ [6,12,96,129,258] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u390

theorem m691_6 : Upper (D 4) (R 4) [6,48,192,257,6] 13 :=
  permutation_upper _ _ _ [6,33,192,6,264] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u483

theorem m691_9 : Upper (D 4) (R 4) [6,48,192,257,9] 13 :=
  permutation_upper _ _ _ [6,24,34,65,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u416

theorem m691_10 : Upper (D 4) (R 4) [6,48,192,257,10] 13 :=
  permutation_upper _ _ _ [6,33,72,18,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u457

theorem m691_12 : Upper (D 4) (R 4) [6,48,192,257,12] 13 :=
  permutation_upper _ _ _ [6,40,192,20,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u517

def r691 : Route 9 := (fun mask => (mask,id))

def c691 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u691 : Upper (D 4) (R 4) [6,48,192,257] 13 := by
  apply FastRouting.sound _ _ [6,48,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12] r691 c691
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m691_3
  · exact m691_5
  · exact m691_6
  · exact m691_9
  · exact m691_10
  · exact m691_12

theorem m692_3 : Upper (D 4) (R 4) [6,48,192,260,3] 13 :=
  permutation_upper _ _ _ [6,12,33,192,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u353

theorem m692_9 : Upper (D 4) (R 4) [6,48,192,260,9] 13 :=
  permutation_upper _ _ _ [6,24,40,192,257] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 8 | 6 => 6 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u430

theorem m692_10 : Upper (D 4) (R 4) [6,48,192,260,10] 13 :=
  permutation_upper _ _ _ [6,33,72,384,10] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u480

def r692 : Route 9 := (fun mask => (mask,id))

def c692 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u692 : Upper (D 4) (R 4) [6,48,192,260] 13 := by
  apply FastRouting.sound _ _ [6,48,192,260] 13 (by decide) (choices 2) [3,9,10] r692 c692
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m692_3
  · exact m692_9
  · exact m692_10

def b693 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 7 98 388 14 25 57 89 153 281), lower := (rows 7 98 388 14 16 32 64 128 256), losses := [] }

theorem u693 : Upper (D 4) (R 4) [6,96,384,6] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b693
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m694_3 : Upper (D 4) (R 4) [6,96,384,17,3] 13 :=
  permutation_upper _ _ _ [6,12,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u338

theorem m694_5 : Upper (D 4) (R 4) [6,96,384,17,5] 13 :=
  permutation_upper _ _ _ [6,12,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u338

theorem m694_6 : Upper (D 4) (R 4) [6,96,384,17,6] 13 :=
  permutation_upper _ _ _ [6,24,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u403

theorem m694_9 : Upper (D 4) (R 4) [6,96,384,17,9] 13 :=
  permutation_upper _ _ _ [6,5,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u225

theorem m694_10 : Upper (D 4) (R 4) [6,96,384,17,10] 13 :=
  permutation_upper _ _ _ [6,9,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u280

theorem m694_12 : Upper (D 4) (R 4) [6,96,384,17,12] 13 :=
  permutation_upper _ _ _ [6,9,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 0 | 3 => 2 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 4 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u280

def r694 : Route 9 := (fun mask => (mask,id))

def c694 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u694 : Upper (D 4) (R 4) [6,96,384,17] 13 := by
  apply FastRouting.sound _ _ [6,96,384,17] 13 (by decide) (choices 2) [3,5,6,9,10,12] r694 c694
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m694_3
  · exact m694_5
  · exact m694_6
  · exact m694_9
  · exact m694_10
  · exact m694_12

theorem m695_5 : Upper (D 4) (R 4) [6,96,384,18,5] 13 :=
  permutation_upper _ _ _ [6,12,96,384,9] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 7 | 6 => 8 | 7 => 5 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u399

theorem m695_9 : Upper (D 4) (R 4) [6,96,384,18,9] 13 :=
  permutation_upper _ _ _ [6,9,24,96,384] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u280

theorem m695_12 : Upper (D 4) (R 4) [6,96,384,18,12] 13 :=
  permutation_upper _ _ _ [6,9,96,384,12] (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u333

def r695 : Route 9 := (fun mask => (mask,id))

def c695 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u695 : Upper (D 4) (R 4) [6,96,384,18] 13 := by
  apply FastRouting.sound _ _ [6,96,384,18] 13 (by decide) (choices 2) [5,9,12] r695 c695
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m695_5
  · exact m695_9
  · exact m695_12

def b696 : PairBound 9 := { available := 398, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 19 19 37 76 414 430 462 398 398), lower := (rows 19 19 37 76 16 32 64 128 256), losses := [] }

theorem u696 : Upper (D 4) (R 4) [18,17,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b696
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b697 : PairBound 9 := { available := 270, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 19 19 37 200 286 302 334 398 270), lower := (rows 19 19 37 200 16 32 64 128 256), losses := [] }

theorem u697 : Upper (D 4) (R 4) [18,17,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b697
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b698 : PairBound 9 := { available := 399, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 19 19 44 76 415 431 463 399 399), lower := (rows 19 19 44 76 16 32 64 128 256), losses := [] }

theorem u698 : Upper (D 4) (R 4) [18,17,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b698
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b699 : PairBound 9 := { available := 271, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 19 19 44 200 287 303 335 399 271), lower := (rows 19 19 44 200 16 32 64 128 256), losses := [] }

theorem u699 : Upper (D 4) (R 4) [18,17,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b699
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b700 : PairBound 9 := { available := 15, camps := [{ cop := 4, region := 3, targets := 4 }], pairs := [(0,2)], upper := (rows 19 19 100 392 31 47 79 143 271), lower := (rows 19 19 100 392 16 32 64 128 256), losses := [] }

theorem u700 : Upper (D 4) (R 4) [18,17,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b700
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b701 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 37 76 411 427 459 395 395), lower := (rows 19 22 37 76 16 32 64 128 256), losses := [] }

theorem u701 : Upper (D 4) (R 4) [18,20,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b701
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b702 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 37 200 287 303 335 399 271), lower := (rows 19 22 37 200 16 32 64 128 256), losses := [] }

theorem u702 : Upper (D 4) (R 4) [18,20,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b702
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b703 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 44 73 415 431 463 399 399), lower := (rows 19 22 44 73 16 32 64 128 256), losses := [] }

theorem u703 : Upper (D 4) (R 4) [18,20,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b703
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b704 : PairBound 9 := { available := 395, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 44 76 411 427 459 395 395), lower := (rows 19 22 44 76 16 32 64 128 256), losses := [] }

theorem u704 : Upper (D 4) (R 4) [18,20,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b704
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b705 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 44 200 287 303 335 399 271), lower := (rows 19 22 44 200 16 32 64 128 256), losses := [] }

theorem u705 : Upper (D 4) (R 4) [18,20,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b705
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b706 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 100 137 287 303 335 399 271), lower := (rows 19 22 100 137 16 32 64 128 256), losses := [] }

theorem u706 : Upper (D 4) (R 4) [18,20,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b706
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b707 : PairBound 9 := { available := 267, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 100 140 283 299 331 395 267), lower := (rows 19 22 100 140 16 32 64 128 256), losses := [] }

theorem u707 : Upper (D 4) (R 4) [18,20,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b707
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b708 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 19 22 100 392 31 47 79 143 271), lower := (rows 19 22 100 392 16 32 64 128 256), losses := [] }

theorem u708 : Upper (D 4) (R 4) [18,20,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b708
    (constants 4).1 (constants 4).2 (by decide +kernel)

theorem m709_6 : Upper (D 4) (R 4) [18,33,65,132,6] 13 :=
  permutation_upper _ _ _ [6,12,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u341

theorem m709_10 : Upper (D 4) (R 4) [18,33,65,132,10] 13 :=
  permutation_upper _ _ _ [6,12,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u346

theorem m709_12 : Upper (D 4) (R 4) [18,33,65,132,12] 13 :=
  permutation_upper _ _ _ [6,24,33,65,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u406

theorem m709_258 : Upper (D 4) (R 4) [18,33,65,132,258] 13 :=
  permutation_upper _ _ _ [6,33,66,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u449

theorem m709_260 : Upper (D 4) (R 4) [18,33,65,132,260] 13 :=
  permutation_upper _ _ _ [6,33,72,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u465

theorem m709_264 : Upper (D 4) (R 4) [18,33,65,132,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u475

def r709 : Route 9 := (fun mask => (mask,id))

def c709 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u709 : Upper (D 4) (R 4) [18,33,65,132] 13 := by
  apply FastRouting.sound _ _ [18,33,65,132] 13 (by decide) (choices 2) [6,10,12,258,260,264] r709 c709
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m709_6
  · exact m709_10
  · exact m709_12
  · exact m709_258
  · exact m709_260
  · exact m709_264

theorem m710_6 : Upper (D 4) (R 4) [18,33,65,384,6] 13 :=
  permutation_upper _ _ _ [6,12,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u342

theorem m710_10 : Upper (D 4) (R 4) [18,33,65,384,10] 13 :=
  permutation_upper _ _ _ [6,12,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u351

theorem m710_12 : Upper (D 4) (R 4) [18,33,65,384,12] 13 :=
  permutation_upper _ _ _ [6,24,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u407

def r710 : Route 9 := (fun mask => (mask,id))

def c710 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u710 : Upper (D 4) (R 4) [18,33,65,384] 13 := by
  apply FastRouting.sound _ _ [18,33,65,384] 13 (by decide) (choices 2) [6,10,12] r710 c710
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m710_6
  · exact m710_10
  · exact m710_12

theorem m711_5 : Upper (D 4) (R 4) [18,33,66,132,5] 13 :=
  permutation_upper _ _ _ [6,9,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u282

theorem m711_9 : Upper (D 4) (R 4) [18,33,66,132,9] 13 :=
  permutation_upper _ _ _ [6,9,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u286

theorem m711_12 : Upper (D 4) (R 4) [18,33,66,132,12] 13 :=
  permutation_upper _ _ _ [6,24,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u411

theorem m711_257 : Upper (D 4) (R 4) [18,33,66,132,257] 13 :=
  permutation_upper _ _ _ [6,33,65,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u444

theorem m711_260 : Upper (D 4) (R 4) [18,33,66,132,260] 13 :=
  permutation_upper _ _ _ [6,33,72,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u469

theorem m711_264 : Upper (D 4) (R 4) [18,33,66,132,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u476

def r711 : Route 9 := (fun mask => (mask,id))

def c711 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u711 : Upper (D 4) (R 4) [18,33,66,132] 13 := by
  apply FastRouting.sound _ _ [18,33,66,132] 13 (by decide) (choices 2) [5,9,12,257,260,264] r711 c711
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m711_5
  · exact m711_9
  · exact m711_12
  · exact m711_257
  · exact m711_260
  · exact m711_264

theorem m712_5 : Upper (D 4) (R 4) [18,33,66,384,5] 13 :=
  permutation_upper _ _ _ [6,9,33,68,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u283

theorem m712_9 : Upper (D 4) (R 4) [18,33,66,384,9] 13 :=
  permutation_upper _ _ _ [6,9,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u291

theorem m712_12 : Upper (D 4) (R 4) [18,33,66,384,12] 13 :=
  permutation_upper _ _ _ [6,24,33,68,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u412

def r712 : Route 9 := (fun mask => (mask,id))

def c712 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u712 : Upper (D 4) (R 4) [18,33,66,384] 13 := by
  apply FastRouting.sound _ _ [18,33,66,384] 13 (by decide) (choices 2) [5,9,12] r712 c712
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m712_5
  · exact m712_9
  · exact m712_12

theorem m713_3 : Upper (D 4) (R 4) [18,33,72,132,3] 13 :=
  permutation_upper _ _ _ [6,5,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u226

theorem m713_5 : Upper (D 4) (R 4) [18,33,72,132,5] 13 :=
  permutation_upper _ _ _ [6,9,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u287

theorem m713_6 : Upper (D 4) (R 4) [18,33,72,132,6] 13 :=
  permutation_upper _ _ _ [6,12,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u348

theorem m713_9 : Upper (D 4) (R 4) [18,33,72,132,9] 13 :=
  permutation_upper _ _ _ [6,9,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u287

theorem m713_10 : Upper (D 4) (R 4) [18,33,72,132,10] 13 :=
  permutation_upper _ _ _ [6,12,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u348

theorem m713_12 : Upper (D 4) (R 4) [18,33,72,132,12] 13 :=
  permutation_upper _ _ _ [6,24,33,80,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u413

theorem m713_257 : Upper (D 4) (R 4) [18,33,72,132,257] 13 :=
  permutation_upper _ _ _ [6,33,65,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u445

theorem m713_258 : Upper (D 4) (R 4) [18,33,72,132,258] 13 :=
  permutation_upper _ _ _ [6,33,66,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u451

theorem m713_260 : Upper (D 4) (R 4) [18,33,72,132,260] 13 :=
  permutation_upper _ _ _ [6,33,72,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u478

theorem m713_264 : Upper (D 4) (R 4) [18,33,72,132,264] 13 :=
  permutation_upper _ _ _ [6,33,72,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u478

def r713 : Route 9 := (fun mask => (mask,id))

def c713 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u713 : Upper (D 4) (R 4) [18,33,72,132] 13 := by
  apply FastRouting.sound _ _ [18,33,72,132] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r713 c713
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m713_3
  · exact m713_5
  · exact m713_6
  · exact m713_9
  · exact m713_10
  · exact m713_12
  · exact m713_257
  · exact m713_258
  · exact m713_260
  · exact m713_264

theorem m714_3 : Upper (D 4) (R 4) [18,33,72,384,3] 13 :=
  permutation_upper _ _ _ [6,5,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u227

theorem m714_5 : Upper (D 4) (R 4) [18,33,72,384,5] 13 :=
  permutation_upper _ _ _ [6,9,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u288

theorem m714_6 : Upper (D 4) (R 4) [18,33,72,384,6] 13 :=
  permutation_upper _ _ _ [6,12,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u349

theorem m714_9 : Upper (D 4) (R 4) [18,33,72,384,9] 13 :=
  permutation_upper _ _ _ [6,9,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u292

theorem m714_10 : Upper (D 4) (R 4) [18,33,72,384,10] 13 :=
  permutation_upper _ _ _ [6,12,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u353

theorem m714_12 : Upper (D 4) (R 4) [18,33,72,384,12] 13 :=
  permutation_upper _ _ _ [6,24,33,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u414

def r714 : Route 9 := (fun mask => (mask,id))

def c714 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u714 : Upper (D 4) (R 4) [18,33,72,384] 13 := by
  apply FastRouting.sound _ _ [18,33,72,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r714 c714
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m714_3
  · exact m714_5
  · exact m714_6
  · exact m714_9
  · exact m714_10
  · exact m714_12

theorem m715_5 : Upper (D 4) (R 4) [18,36,65,130,5] 13 :=
  permutation_upper _ _ _ [6,9,34,68,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u293

theorem m715_9 : Upper (D 4) (R 4) [18,36,65,130,9] 13 :=
  permutation_upper _ _ _ [6,9,40,80,130] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u307

theorem m715_12 : Upper (D 4) (R 4) [18,36,65,130,12] 13 :=
  permutation_upper _ _ _ [6,24,40,65,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u419

theorem m715_257 : Upper (D 4) (R 4) [18,36,65,130,257] 13 :=
  permutation_upper _ _ _ [6,33,72,129,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u464

theorem m715_260 : Upper (D 4) (R 4) [18,36,65,130,260] 13 :=
  permutation_upper _ _ _ [6,40,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u503

theorem m715_264 : Upper (D 4) (R 4) [18,36,65,130,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u509

def r715 : Route 9 := (fun mask => (mask,id))

def c715 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u715 : Upper (D 4) (R 4) [18,36,65,130] 13 := by
  apply FastRouting.sound _ _ [18,36,65,130] 13 (by decide) (choices 2) [5,9,12,257,260,264] r715 c715
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m715_5
  · exact m715_9
  · exact m715_12
  · exact m715_257
  · exact m715_260
  · exact m715_264

theorem m716_3 : Upper (D 4) (R 4) [18,36,65,132,3] 13 :=
  permutation_upper _ _ _ [6,5,40,65,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u230

theorem m716_9 : Upper (D 4) (R 4) [18,36,65,132,9] 13 :=
  permutation_upper _ _ _ [6,9,48,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u317

theorem m716_10 : Upper (D 4) (R 4) [18,36,65,132,10] 13 :=
  permutation_upper _ _ _ [6,12,48,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u380

theorem m716_257 : Upper (D 4) (R 4) [18,36,65,132,257] 13 :=
  permutation_upper _ _ _ [6,33,72,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u465

theorem m716_258 : Upper (D 4) (R 4) [18,36,65,132,258] 13 :=
  permutation_upper _ _ _ [6,36,72,129,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u495

theorem m716_264 : Upper (D 4) (R 4) [18,36,65,132,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u511

def r716 : Route 9 := (fun mask => (mask,id))

def c716 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u716 : Upper (D 4) (R 4) [18,36,65,132] 13 := by
  apply FastRouting.sound _ _ [18,36,65,132] 13 (by decide) (choices 2) [3,9,10,257,258,264] r716 c716
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m716_3
  · exact m716_9
  · exact m716_10
  · exact m716_257
  · exact m716_258
  · exact m716_264

theorem m717_3 : Upper (D 4) (R 4) [18,36,65,384,3] 13 :=
  permutation_upper _ _ _ [6,5,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u231

theorem m717_5 : Upper (D 4) (R 4) [18,36,65,384,5] 13 :=
  permutation_upper _ _ _ [6,9,34,68,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u294

theorem m717_6 : Upper (D 4) (R 4) [18,36,65,384,6] 13 :=
  permutation_upper _ _ _ [6,12,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u365

theorem m717_9 : Upper (D 4) (R 4) [18,36,65,384,9] 13 :=
  permutation_upper _ _ _ [6,9,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u326

theorem m717_10 : Upper (D 4) (R 4) [18,36,65,384,10] 13 :=
  permutation_upper _ _ _ [6,12,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u384

theorem m717_12 : Upper (D 4) (R 4) [18,36,65,384,12] 13 :=
  permutation_upper _ _ _ [6,24,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u420

def r717 : Route 9 := (fun mask => (mask,id))

def c717 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u717 : Upper (D 4) (R 4) [18,36,65,384] 13 := by
  apply FastRouting.sound _ _ [18,36,65,384] 13 (by decide) (choices 2) [3,5,6,9,10,12] r717 c717
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m717_3
  · exact m717_5
  · exact m717_6
  · exact m717_9
  · exact m717_10
  · exact m717_12

theorem m718_5 : Upper (D 4) (R 4) [18,36,66,129,5] 13 :=
  permutation_upper _ _ _ [6,9,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u304

theorem m718_9 : Upper (D 4) (R 4) [18,36,66,129,9] 13 :=
  permutation_upper _ _ _ [6,9,34,80,136] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u298

theorem m718_12 : Upper (D 4) (R 4) [18,36,66,129,12] 13 :=
  permutation_upper _ _ _ [6,24,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u424

theorem m718_257 : Upper (D 4) (R 4) [18,36,66,129,257] 13 :=
  permutation_upper _ _ _ [6,33,72,132,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u471

theorem m718_260 : Upper (D 4) (R 4) [18,36,66,129,260] 13 :=
  permutation_upper _ _ _ [6,40,72,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u504

theorem m718_264 : Upper (D 4) (R 4) [18,36,66,129,264] 13 :=
  permutation_upper _ _ _ [6,40,80,129,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 8 | 6 => 5 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 6 | 6 => 8 | 7 => 7 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u510

def r718 : Route 9 := (fun mask => (mask,id))

def c718 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u718 : Upper (D 4) (R 4) [18,36,66,129] 13 := by
  apply FastRouting.sound _ _ [18,36,66,129] 13 (by decide) (choices 2) [5,9,12,257,260,264] r718 c718
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m718_5
  · exact m718_9
  · exact m718_12
  · exact m718_257
  · exact m718_260
  · exact m718_264

theorem m719_9 : Upper (D 4) (R 4) [18,36,66,132,9] 13 :=
  permutation_upper _ _ _ [6,9,48,80,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u318

theorem m719_257 : Upper (D 4) (R 4) [18,36,66,132,257] 13 :=
  permutation_upper _ _ _ [6,33,72,132,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 8 | 6 => 5 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 7 | 7 => 8 | _ => 5) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u473

theorem m719_264 : Upper (D 4) (R 4) [18,36,66,132,264] 13 :=
  permutation_upper _ _ _ [6,40,80,130,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u513

def r719 : Route 9 := (fun mask => (mask,id))

def c719 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u719 : Upper (D 4) (R 4) [18,36,66,132] 13 := by
  apply FastRouting.sound _ _ [18,36,66,132] 13 (by decide) (choices 2) [9,257,264] r719 c719
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m719_9
  · exact m719_257
  · exact m719_264

#print axioms u719
end Delivery.IrregularNine14.P04
