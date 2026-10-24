import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0090
import IrregularNine14P03C0091
import IrregularNine14P03C0092
import IrregularNine14P03C0093
import IrregularNine14P03C0094
import IrregularNine14P03C0095
import IrregularNine14P03C0096
import IrregularNine14P03C0097
import IrregularNine14P03C0098
import IrregularNine14P03C0099

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b7500 : PairBound 9 := { available := 103, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 140 152 119 103 103 231 359), lower := (rows 289 67 140 152 16 32 64 128 256), losses := [] }

theorem u7500 : Upper (D 3) (R 3) [288,65,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7500
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7501 : PairBound 9 := { available := 87, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 140 168 87 119 87 215 343), lower := (rows 289 67 140 168 16 32 64 128 256), losses := [] }

theorem u7501 : Upper (D 3) (R 3) [288,65,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7501
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7502 : PairBound 9 := { available := 55, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 289 67 140 200 55 55 119 183 311), lower := (rows 289 67 140 200 16 32 64 128 256), losses := [] }

theorem u7502 : Upper (D 3) (R 3) [288,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7502
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7503_3 : Upper (D 3) (R 3) [288,65,144,160,3] 13 :=
  permutation_upper _ _ _ [288,5,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5453

theorem m7503_5 : Upper (D 3) (R 3) [288,65,144,160,5] 13 :=
  permutation_upper _ _ _ [288,5,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5474

theorem m7503_6 : Upper (D 3) (R 3) [288,65,144,160,6] 13 :=
  permutation_upper _ _ _ [288,12,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5646

theorem m7503_9 : Upper (D 3) (R 3) [288,65,144,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5561

theorem m7503_10 : Upper (D 3) (R 3) [288,65,144,160,10] 13 :=
  permutation_upper _ _ _ [288,12,65,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5660

theorem m7503_12 : Upper (D 3) (R 3) [288,65,144,160,12] 13 :=
  permutation_upper _ _ _ [288,12,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5668

theorem m7503_65 : Upper (D 3) (R 3) [288,65,144,160,65] 13 :=
  permutation_upper _ _ _ [288,65,65,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5753

theorem m7503_66 : Upper (D 3) (R 3) [288,65,144,160,66] 13 :=
  permutation_upper _ _ _ [288,65,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5756

theorem m7503_68 : Upper (D 3) (R 3) [288,65,144,160,68] 13 :=
  permutation_upper _ _ _ [288,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5764

theorem m7503_72 : Upper (D 3) (R 3) [288,65,144,160,72] 13 :=
  permutation_upper _ _ _ [288,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5770

def r7503 : Route 9 := (fun mask => (mask,id))

def c7503 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7503 : Upper (D 3) (R 3) [288,65,144,160] 13 := by
  apply FastRouting.sound _ _ [288,65,144,160] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r7503 c7503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7503_3
  · exact m7503_5
  · exact m7503_6
  · exact m7503_9
  · exact m7503_10
  · exact m7503_12
  · exact m7503_65
  · exact m7503_66
  · exact m7503_68
  · exact m7503_72

theorem m7504_3 : Upper (D 3) (R 3) [288,65,144,192,3] 13 :=
  permutation_upper _ _ _ [288,5,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5454

theorem m7504_5 : Upper (D 3) (R 3) [288,65,144,192,5] 13 :=
  permutation_upper _ _ _ [288,5,66,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5479

theorem m7504_6 : Upper (D 3) (R 3) [288,65,144,192,6] 13 :=
  permutation_upper _ _ _ [288,12,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5647

theorem m7504_9 : Upper (D 3) (R 3) [288,65,144,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5586

theorem m7504_10 : Upper (D 3) (R 3) [288,65,144,192,10] 13 :=
  permutation_upper _ _ _ [288,12,65,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5664

theorem m7504_12 : Upper (D 3) (R 3) [288,65,144,192,12] 13 :=
  permutation_upper _ _ _ [288,12,66,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5678

theorem m7504_33 : Upper (D 3) (R 3) [288,65,144,192,33] 13 :=
  permutation_upper _ _ _ [288,33,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5701

theorem m7504_34 : Upper (D 3) (R 3) [288,65,144,192,34] 13 :=
  permutation_upper _ _ _ [288,36,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5717

theorem m7504_36 : Upper (D 3) (R 3) [288,65,144,192,36] 13 :=
  permutation_upper _ _ _ [288,36,66,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5724

theorem m7504_40 : Upper (D 3) (R 3) [288,65,144,192,40] 13 :=
  permutation_upper _ _ _ [288,36,192,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5746

def r7504 : Route 9 := (fun mask => (mask,id))

def c7504 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7504 : Upper (D 3) (R 3) [288,65,144,192] 13 := by
  apply FastRouting.sound _ _ [288,65,144,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r7504 c7504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7504_3
  · exact m7504_5
  · exact m7504_6
  · exact m7504_9
  · exact m7504_10
  · exact m7504_12
  · exact m7504_33
  · exact m7504_34
  · exact m7504_36
  · exact m7504_40

theorem m7505_3 : Upper (D 3) (R 3) [288,65,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5455

theorem m7505_5 : Upper (D 3) (R 3) [288,65,160,192,5] 13 :=
  permutation_upper _ _ _ [288,5,96,129,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5567

theorem m7505_6 : Upper (D 3) (R 3) [288,65,160,192,6] 13 :=
  permutation_upper _ _ _ [288,12,65,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5661

theorem m7505_9 : Upper (D 3) (R 3) [288,65,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5588

theorem m7505_10 : Upper (D 3) (R 3) [288,65,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,65,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5665

theorem m7505_12 : Upper (D 3) (R 3) [288,65,160,192,12] 13 :=
  permutation_upper _ _ _ [288,12,96,192,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5691

def r7505 : Route 9 := (fun mask => (mask,id))

def c7505 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7505 : Upper (D 3) (R 3) [288,65,160,192] 13 := by
  apply FastRouting.sound _ _ [288,65,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7505 c7505
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7505_3
  · exact m7505_5
  · exact m7505_6
  · exact m7505_9
  · exact m7505_10
  · exact m7505_12

def b7506 : PairBound 9 := { available := 153, camps := [{ cop := 6, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 70 70 168 153 185 217 153 409), lower := (rows 289 70 70 168 16 32 64 128 256), losses := [] }

theorem u7506 : Upper (D 3) (R 3) [288,68,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7506
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7507 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 138 177 177 241 177 433), lower := (rows 289 70 76 138 16 32 64 128 256), losses := [] }

theorem u7507 : Upper (D 3) (R 3) [288,68,72,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7507
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7508 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 76 168 147 179 211 147 403), lower := (rows 289 70 76 168 16 32 64 128 256), losses := [] }

theorem u7508 : Upper (D 3) (R 3) [288,68,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7508
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7509 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 84 138 185 169 233 169 425), lower := (rows 289 70 84 138 16 32 64 128 256), losses := [] }

theorem u7509 : Upper (D 3) (R 3) [288,68,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7509
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7510 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 425, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 84 168 155 171 203 139 395), lower := (rows 289 70 84 168 16 32 64 128 256), losses := [] }

theorem u7510 : Upper (D 3) (R 3) [288,68,80,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7510
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7511 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 100 138 153 185 217 153 409), lower := (rows 289 70 100 138 16 32 64 128 256), losses := [] }

theorem u7511 : Upper (D 3) (R 3) [288,68,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7511
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7512 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 134 88 185 169 233 169 425), lower := (rows 289 70 134 88 16 32 64 128 256), losses := [] }

theorem u7512 : Upper (D 3) (R 3) [288,68,130,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7512
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7513 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 134 104 153 185 217 153 409), lower := (rows 289 70 134 104 16 32 64 128 256), losses := [] }

theorem u7513 : Upper (D 3) (R 3) [288,68,130,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7513
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7514 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 70 134 200 57 57 121 185 313), lower := (rows 289 70 134 200 16 32 64 128 256), losses := [] }

theorem u7514 : Upper (D 3) (R 3) [288,68,130,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7514
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7515 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 140 88 179 163 227 163 419), lower := (rows 289 70 140 88 16 32 64 128 256), losses := [] }

theorem u7515 : Upper (D 3) (R 3) [288,68,136,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7515
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7516 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 140 104 147 179 211 147 403), lower := (rows 289 70 140 104 16 32 64 128 256), losses := [] }

theorem u7516 : Upper (D 3) (R 3) [288,68,136,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7516
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7517 : PairBound 9 := { available := 51, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 70 140 200 51 51 115 179 307), lower := (rows 289 70 140 200 16 32 64 128 256), losses := [] }

theorem u7517 : Upper (D 3) (R 3) [288,68,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7517
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7518_3 : Upper (D 3) (R 3) [288,68,144,96,3] 13 :=
  permutation_upper _ _ _ [288,5,72,130,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5530

theorem m7518_9 : Upper (D 3) (R 3) [288,68,144,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5564

theorem m7518_10 : Upper (D 3) (R 3) [288,68,144,96,10] 13 :=
  permutation_upper _ _ _ [288,12,80,96,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5681

theorem m7518_129 : Upper (D 3) (R 3) [288,68,144,96,129] 13 :=
  permutation_upper _ _ _ [288,65,66,132,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5756

theorem m7518_130 : Upper (D 3) (R 3) [288,68,144,96,130] 13 :=
  permutation_upper _ _ _ [288,68,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5775

theorem m7518_136 : Upper (D 3) (R 3) [288,68,144,96,136] 13 :=
  permutation_upper _ _ _ [288,68,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5776

def r7518 : Route 9 := (fun mask => (mask,id))

def c7518 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7518 : Upper (D 3) (R 3) [288,68,144,96] 13 := by
  apply FastRouting.sound _ _ [288,68,144,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r7518 c7518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7518_3
  · exact m7518_9
  · exact m7518_10
  · exact m7518_129
  · exact m7518_130
  · exact m7518_136

theorem m7519_3 : Upper (D 3) (R 3) [288,68,144,160,3] 13 :=
  permutation_upper _ _ _ [288,5,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5532

theorem m7519_9 : Upper (D 3) (R 3) [288,68,144,160,9] 13 :=
  permutation_upper _ _ _ [288,5,96,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5562

theorem m7519_10 : Upper (D 3) (R 3) [288,68,144,160,10] 13 :=
  permutation_upper _ _ _ [288,12,80,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5685

theorem m7519_65 : Upper (D 3) (R 3) [288,68,144,160,65] 13 :=
  permutation_upper _ _ _ [288,65,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5761

theorem m7519_66 : Upper (D 3) (R 3) [288,68,144,160,66] 13 :=
  permutation_upper _ _ _ [288,68,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5775

theorem m7519_72 : Upper (D 3) (R 3) [288,68,144,160,72] 13 :=
  permutation_upper _ _ _ [288,68,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5778

def r7519 : Route 9 := (fun mask => (mask,id))

def c7519 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7519 : Upper (D 3) (R 3) [288,68,144,160] 13 := by
  apply FastRouting.sound _ _ [288,68,144,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7519 c7519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7519_3
  · exact m7519_9
  · exact m7519_10
  · exact m7519_65
  · exact m7519_66
  · exact m7519_72

theorem m7520_3 : Upper (D 3) (R 3) [288,68,144,192,3] 13 :=
  permutation_upper _ _ _ [288,5,72,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5533

theorem m7520_9 : Upper (D 3) (R 3) [288,68,144,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5589

theorem m7520_10 : Upper (D 3) (R 3) [288,68,144,192,10] 13 :=
  permutation_upper _ _ _ [288,12,80,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5689

theorem m7520_33 : Upper (D 3) (R 3) [288,68,144,192,33] 13 :=
  permutation_upper _ _ _ [288,33,66,132,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5703

theorem m7520_34 : Upper (D 3) (R 3) [288,68,144,192,34] 13 :=
  permutation_upper _ _ _ [288,36,72,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5737

theorem m7520_40 : Upper (D 3) (R 3) [288,68,144,192,40] 13 :=
  permutation_upper _ _ _ [288,36,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5748

def r7520 : Route 9 := (fun mask => (mask,id))

def c7520 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7520 : Upper (D 3) (R 3) [288,68,144,192] 13 := by
  apply FastRouting.sound _ _ [288,68,144,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r7520 c7520
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7520_3
  · exact m7520_9
  · exact m7520_10
  · exact m7520_33
  · exact m7520_34
  · exact m7520_40

theorem m7521_3 : Upper (D 3) (R 3) [288,68,160,80,3] 13 :=
  permutation_upper _ _ _ [288,5,72,160,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5544

theorem m7521_9 : Upper (D 3) (R 3) [288,68,160,80,9] 13 :=
  permutation_upper _ _ _ [288,5,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5473

theorem m7521_10 : Upper (D 3) (R 3) [288,68,160,80,10] 13 :=
  permutation_upper _ _ _ [288,12,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5667

theorem m7521_129 : Upper (D 3) (R 3) [288,68,160,80,129] 13 :=
  permutation_upper _ _ _ [288,65,96,130,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5771

theorem m7521_130 : Upper (D 3) (R 3) [288,68,160,80,130] 13 :=
  permutation_upper _ _ _ [288,68,136,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5778

theorem m7521_136 : Upper (D 3) (R 3) [288,68,160,80,136] 13 :=
  permutation_upper _ _ _ [288,68,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5777

def r7521 : Route 9 := (fun mask => (mask,id))

def c7521 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7521 : Upper (D 3) (R 3) [288,68,160,80] 13 := by
  apply FastRouting.sound _ _ [288,68,160,80] 13 (by decide) (choices 2) [3,9,10,129,130,136] r7521 c7521
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7521_3
  · exact m7521_9
  · exact m7521_10
  · exact m7521_129
  · exact m7521_130
  · exact m7521_136

theorem m7522_3 : Upper (D 3) (R 3) [288,68,160,144,3] 13 :=
  permutation_upper _ _ _ [288,5,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5546

theorem m7522_9 : Upper (D 3) (R 3) [288,68,160,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5475

theorem m7522_10 : Upper (D 3) (R 3) [288,68,160,144,10] 13 :=
  permutation_upper _ _ _ [288,12,66,144,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5671

theorem m7522_65 : Upper (D 3) (R 3) [288,68,160,144,65] 13 :=
  permutation_upper _ _ _ [288,65,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5769

theorem m7522_66 : Upper (D 3) (R 3) [288,68,160,144,66] 13 :=
  permutation_upper _ _ _ [288,68,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5776

theorem m7522_72 : Upper (D 3) (R 3) [288,68,160,144,72] 13 :=
  permutation_upper _ _ _ [288,68,130,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5777

def r7522 : Route 9 := (fun mask => (mask,id))

def c7522 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7522 : Upper (D 3) (R 3) [288,68,160,144] 13 := by
  apply FastRouting.sound _ _ [288,68,160,144] 13 (by decide) (choices 2) [3,9,10,65,66,72] r7522 c7522
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7522_3
  · exact m7522_9
  · exact m7522_10
  · exact m7522_65
  · exact m7522_66
  · exact m7522_72

theorem m7523_3 : Upper (D 3) (R 3) [288,68,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5547

theorem m7523_9 : Upper (D 3) (R 3) [288,68,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5592

theorem m7523_10 : Upper (D 3) (R 3) [288,68,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,80,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5690

def r7523 : Route 9 := (fun mask => (mask,id))

def c7523 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7523 : Upper (D 3) (R 3) [288,68,160,192] 13 := by
  apply FastRouting.sound _ _ [288,68,160,192] 13 (by decide) (choices 2) [3,9,10] r7523 c7523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7523_3
  · exact m7523_9
  · exact m7523_10

def b7524 : PairBound 9 := { available := 27, camps := [{ cop := 1, region := 441, targets := 64 }], pairs := [(0,6)], upper := (rows 289 70 196 168 27 59 91 155 283), lower := (rows 289 70 196 168 16 32 64 128 256), losses := [] }

theorem u7524 : Upper (D 3) (R 3) [288,68,192,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7524
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7525_3 : Upper (D 3) (R 3) [288,80,160,192,3] 13 :=
  permutation_upper _ _ _ [288,5,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5483

theorem m7525_5 : Upper (D 3) (R 3) [288,80,160,192,5] 13 :=
  permutation_upper _ _ _ [288,5,96,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5568

theorem m7525_6 : Upper (D 3) (R 3) [288,80,160,192,6] 13 :=
  permutation_upper _ _ _ [288,12,66,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5677

theorem m7525_9 : Upper (D 3) (R 3) [288,80,160,192,9] 13 :=
  permutation_upper _ _ _ [288,5,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5590

theorem m7525_10 : Upper (D 3) (R 3) [288,80,160,192,10] 13 :=
  permutation_upper _ _ _ [288,12,66,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5679

theorem m7525_12 : Upper (D 3) (R 3) [288,80,160,192,12] 13 :=
  permutation_upper _ _ _ [288,12,96,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5692

def r7525 : Route 9 := (fun mask => (mask,id))

def c7525 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7525 : Upper (D 3) (R 3) [288,80,160,192] 13 := by
  apply FastRouting.sound _ _ [288,80,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12] r7525 c7525
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7525_3
  · exact m7525_5
  · exact m7525_6
  · exact m7525_9
  · exact m7525_10
  · exact m7525_12

def r7526 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c7526 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7526 : Upper (D 3) (R 3) [6,9,17] 13 := by
  apply FastRouting.sound _ _ [6,9,17] 13 (by decide) (choices 2) [33,96,257,288] r7526 c7526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5779
  · exact u5780
  · exact u5781
  · exact u5782

def r7527 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7527 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7527 : Upper (D 3) (R 3) [6,9,33] 13 := by
  apply FastRouting.sound _ _ [6,9,33] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r7527 c7527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5783
  · exact u5784
  · exact u5785
  · exact u5786
  · exact u5787
  · exact u5788
  · exact u5789
  · exact u5790
  · exact u5791
  · exact u5792
  · exact u5793

def r7528 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7528 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7528 : Upper (D 3) (R 3) [6,9,48] 13 := by
  apply FastRouting.sound _ _ [6,9,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r7528 c7528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5794
  · exact u5795
  · exact u5796
  · exact u5797
  · exact u5798
  · exact u5799
  · exact u5800

def r7529 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7529 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7529 : Upper (D 3) (R 3) [6,9,96] 13 := by
  apply FastRouting.sound _ _ [6,9,96] 13 (by decide) (choices 2) [17,33,48,96,129,144,160,257,272,288,384] r7529 c7529
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5801
  · exact u5802
  · exact u5803
  · exact u5804
  · exact u5805
  · exact u5806
  · exact u5807
  · exact u5808
  · exact u5809
  · exact u5810
  · exact u5811

def r7530 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c7530 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7530 : Upper (D 3) (R 3) [6,9,257] 13 := by
  apply FastRouting.sound _ _ [6,9,257] 13 (by decide) (choices 2) [17,33,48,96] r7530 c7530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5812
  · exact u5813
  · exact u5814
  · exact u5815

def r7531 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c7531 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7531 : Upper (D 3) (R 3) [6,9,272] 13 := by
  apply FastRouting.sound _ _ [6,9,272] 13 (by decide) (choices 2) [33,96] r7531 c7531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5816
  · exact u5817

def r7532 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7532 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7532 : Upper (D 3) (R 3) [6,9,288] 13 := by
  apply FastRouting.sound _ _ [6,9,288] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7532 c7532
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5818
  · exact u5819
  · exact u5820
  · exact u5821
  · exact u5822
  · exact u5823
  · exact u5824

def r7533 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7533 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7533 : Upper (D 3) (R 3) [6,24,33] 13 := by
  apply FastRouting.sound _ _ [6,24,33] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r7533 c7533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5825
  · exact u5826
  · exact u5827
  · exact u5828
  · exact u5829
  · exact u5830
  · exact u5831

def r7534 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7534 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7534 : Upper (D 3) (R 3) [6,24,96] 13 := by
  apply FastRouting.sound _ _ [6,24,96] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r7534 c7534
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5832
  · exact u5833
  · exact u5834
  · exact u5835
  · exact u5836
  · exact u5837
  · exact u5838

def r7535 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c7535 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7535 : Upper (D 3) (R 3) [6,24,257] 13 := by
  apply FastRouting.sound _ _ [6,24,257] 13 (by decide) (choices 2) [33,96] r7535 c7535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u5839
  · exact u5840

def r7536 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7536 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7536 : Upper (D 3) (R 3) [6,24,288] 13 := by
  apply FastRouting.sound _ _ [6,24,288] 13 (by decide) (choices 2) [33,65,96,192] r7536 c7536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5841
  · exact u5842
  · exact u5843
  · exact u5844

def b7537 : PairBound 9 := { available := 473, camps := [{ cop := 5, region := 7, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 37 473 473 505 473 473 473), lower := (rows 7 35 37 8 16 32 64 128 256), losses := [] }

theorem u7537 : Upper (D 3) (R 3) [6,33,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7537
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7538 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 44 473 465 497 465 465 465), lower := (rows 7 35 44 8 16 32 64 128 256), losses := [] }

theorem u7538 : Upper (D 3) (R 3) [6,33,40] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7538
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7539_65 : Upper (D 3) (R 3) [6,33,65,65] 13 :=
  permutation_upper _ _ _ [6,33,65,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5846

theorem m7539_80 : Upper (D 3) (R 3) [6,33,65,80] 13 :=
  permutation_upper _ _ _ [6,33,65,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5847

theorem m7539_192 : Upper (D 3) (R 3) [6,33,65,192] 13 :=
  permutation_upper _ _ _ [6,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5851

theorem m7539_320 : Upper (D 3) (R 3) [6,33,65,320] 13 :=
  permutation_upper _ _ _ [6,33,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5854

def r7539 : Route 9 := (fun mask => (mask,id))

def c7539 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7539 : Upper (D 3) (R 3) [6,33,65] 13 := by
  apply FastRouting.sound _ _ [6,33,65] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7539 c7539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5845
  · exact u5846
  · exact u5847
  · exact m7539_65
  · exact m7539_80
  · exact u5848
  · exact u5849
  · exact u5850
  · exact u5851
  · exact m7539_192
  · exact u5852
  · exact u5853
  · exact u5854
  · exact m7539_320
  · exact u5855

def r7540 : Route 9 := (fun mask => (mask,id))

def c7540 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7540 : Upper (D 3) (R 3) [6,33,72] 13 := by
  apply FastRouting.sound _ _ [6,33,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,257,272,288,320,384] r7540 c7540
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5856
  · exact u5857
  · exact u5858
  · exact u5859
  · exact u5860
  · exact u5861
  · exact u5862
  · exact u5863
  · exact u5864
  · exact u5865
  · exact u5866
  · exact u5867
  · exact u5868
  · exact u5869
  · exact u5870

def b7541 : PairBound 9 := { available := 473, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 100 473 473 505 473 473 473), lower := (rows 7 35 100 8 16 32 64 128 256), losses := [] }

theorem u7541 : Upper (D 3) (R 3) [6,33,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7541
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7542 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7542 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7542 : Upper (D 3) (R 3) [6,33,192] 13 := by
  apply FastRouting.sound _ _ [6,33,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r7542 c7542
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5871
  · exact u5872
  · exact u5873
  · exact u5874
  · exact u5875
  · exact u5876
  · exact u5877
  · exact u5878
  · exact u5879
  · exact u5880
  · exact u5881

def r7543 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7543 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7543 : Upper (D 3) (R 3) [6,33,257] 13 := by
  apply FastRouting.sound _ _ [6,33,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7543 c7543
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5882
  · exact u5883
  · exact u5884
  · exact u5885
  · exact u5886
  · exact u5887
  · exact u5888

def r7544 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7544 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7544 : Upper (D 3) (R 3) [6,33,264] 13 := by
  apply FastRouting.sound _ _ [6,33,264] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7544 c7544
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5889
  · exact u5890
  · exact u5891
  · exact u5892
  · exact u5893
  · exact u5894
  · exact u5895

def b7545 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 3, targets := 64 }], pairs := [(0,6)], upper := (rows 7 35 292 217 217 249 217 217 473), lower := (rows 7 35 292 8 16 32 64 128 256), losses := [] }

theorem u7545 : Upper (D 3) (R 3) [6,33,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7545
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7546 : Route 9 := (fun mask => (mask,id))

def c7546 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7546 : Upper (D 3) (R 3) [6,33,320] 13 := by
  apply FastRouting.sound _ _ [6,33,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7546 c7546
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5896
  · exact u5897
  · exact u5898
  · exact u5899
  · exact u5900
  · exact u5901
  · exact u5902
  · exact u5903
  · exact u5904
  · exact u5905

def b7547 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 52 457 465 481 449 449 449), lower := (rows 7 42 52 8 16 32 64 128 256), losses := [] }

theorem u7547 : Upper (D 3) (R 3) [6,40,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7547
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7548 : Route 9 := (fun mask => (mask,id))

def c7548 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u7548 : Upper (D 3) (R 3) [6,40,80] 13 := by
  apply FastRouting.sound _ _ [6,40,80] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r7548 c7548
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5906
  · exact u5907
  · exact u5908
  · exact u5909
  · exact u5910
  · exact u5911
  · exact u5912
  · exact u5913
  · exact u5914
  · exact u5915

def b7549 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 100 473 465 497 465 465 465), lower := (rows 7 42 100 8 16 32 64 128 256), losses := [] }

theorem u7549 : Upper (D 3) (R 3) [6,40,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7549
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7550 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7550 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u7550 : Upper (D 3) (R 3) [6,40,192] 13 := by
  apply FastRouting.sound _ _ [6,40,192] 13 (by decide) (choices 2) [17,33,48,65,80,96,192,257,272,288,320] r7550 c7550
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5916
  · exact u5917
  · exact u5918
  · exact u5919
  · exact u5920
  · exact u5921
  · exact u5922
  · exact u5923
  · exact u5924
  · exact u5925
  · exact u5926

def r7551 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7551 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7551 : Upper (D 3) (R 3) [6,40,257] 13 := by
  apply FastRouting.sound _ _ [6,40,257] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r7551 c7551
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5927
  · exact u5928
  · exact u5929
  · exact u5930
  · exact u5931
  · exact u5932
  · exact u5933

def r7552 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7552 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7552 : Upper (D 3) (R 3) [6,40,272] 13 := by
  apply FastRouting.sound _ _ [6,40,272] 13 (by decide) (choices 2) [33,65,96,192] r7552 c7552
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5934
  · exact u5935
  · exact u5936
  · exact u5937

def b7553 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 292 217 209 241 209 209 465), lower := (rows 7 42 292 8 16 32 64 128 256), losses := [] }

theorem u7553 : Upper (D 3) (R 3) [6,40,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7553
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7554 : Route 9 := (fun mask => (mask,id))

def c7554 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7554 : Upper (D 3) (R 3) [6,40,320] 13 := by
  apply FastRouting.sound _ _ [6,40,320] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192] r7554 c7554
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5938
  · exact u5939
  · exact u5940
  · exact u5941
  · exact u5942
  · exact u5943
  · exact u5944
  · exact u5945
  · exact u5946
  · exact u5947

def b7555 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 100 409 409 441 473 409 409), lower := (rows 7 98 100 8 16 32 64 128 256), losses := [] }

theorem u7555 : Upper (D 3) (R 3) [6,96,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7555
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7556 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 164 473 473 505 473 473 473), lower := (rows 7 98 164 8 16 32 64 128 256), losses := [] }

theorem u7556 : Upper (D 3) (R 3) [6,96,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7556
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7557 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7557 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7557 : Upper (D 3) (R 3) [6,96,257] 13 := by
  apply FastRouting.sound _ _ [6,96,257] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r7557 c7557
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5948
  · exact u5949
  · exact u5950
  · exact u5951
  · exact u5952
  · exact u5953
  · exact u5954

def r7558 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7558 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7558 : Upper (D 3) (R 3) [6,96,264] 13 := by
  apply FastRouting.sound _ _ [6,96,264] 13 (by decide) (choices 2) [17,33,48,96,129,144,160] r7558 c7558
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5955
  · exact u5956
  · exact u5957
  · exact u5958
  · exact u5959
  · exact u5960
  · exact u5961

def b7559 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 7 98 292 217 217 249 217 217 473), lower := (rows 7 98 292 8 16 32 64 128 256), losses := [] }

theorem u7559 : Upper (D 3) (R 3) [6,96,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7559
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u7559
end Delivery.IrregularNine14.P03
