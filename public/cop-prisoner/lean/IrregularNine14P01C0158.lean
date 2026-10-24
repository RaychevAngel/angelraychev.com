import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0143
import IrregularNine14P01C0144
import IrregularNine14P01C0145
import IrregularNine14P01C0146
import IrregularNine14P01C0147
import IrregularNine14P01C0148
import IrregularNine14P01C0149
import IrregularNine14P01C0150
import IrregularNine14P01C0151

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9480_3 : Upper (D 1) (R 1) [304,80,130,3] 13 :=
  permutation_upper _ _ _ [304,80,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8593

theorem m9480_5 : Upper (D 1) (R 1) [304,80,130,5] 13 :=
  permutation_upper _ _ _ [304,80,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8603

theorem m9480_6 : Upper (D 1) (R 1) [304,80,130,6] 13 :=
  permutation_upper _ _ _ [304,80,10,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8616

theorem m9480_33 : Upper (D 1) (R 1) [304,80,130,33] 13 :=
  permutation_upper _ _ _ [304,80,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8621

theorem m9480_34 : Upper (D 1) (R 1) [304,80,130,34] 13 :=
  permutation_upper _ _ _ [304,80,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8628

theorem m9480_36 : Upper (D 1) (R 1) [304,80,130,36] 13 :=
  permutation_upper _ _ _ [304,80,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8635

theorem m9480_65 : Upper (D 1) (R 1) [304,80,130,65] 13 :=
  permutation_upper _ _ _ [304,80,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8638

theorem m9480_66 : Upper (D 1) (R 1) [304,80,130,66] 13 :=
  permutation_upper _ _ _ [304,80,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8642

theorem m9480_68 : Upper (D 1) (R 1) [304,80,130,68] 13 :=
  permutation_upper _ _ _ [304,80,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8646

theorem m9480_96 : Upper (D 1) (R 1) [304,80,130,96] 13 :=
  permutation_upper _ _ _ [304,80,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8650

theorem m9480_129 : Upper (D 1) (R 1) [304,80,130,129] 13 :=
  permutation_upper _ _ _ [304,80,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8652

def r9480 : Route 9 := (fun mask => (mask,id))

def c9480 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9480 : Upper (D 1) (R 1) [304,80,130] 13 := by
  apply FastRouting.sound _ _ [304,80,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r9480 c9480
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9480_3
  · exact m9480_5
  · exact m9480_6
  · exact m9480_33
  · exact m9480_34
  · exact m9480_36
  · exact m9480_65
  · exact m9480_66
  · exact m9480_68
  · exact m9480_96
  · exact m9480_129
  · exact u8656
  · exact u8657
  · exact u8658
  · exact u8659

theorem m9481_3 : Upper (D 1) (R 1) [304,80,136,3] 13 :=
  permutation_upper _ _ _ [304,80,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8594

theorem m9481_5 : Upper (D 1) (R 1) [304,80,136,5] 13 :=
  permutation_upper _ _ _ [304,80,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8604

theorem m9481_6 : Upper (D 1) (R 1) [304,80,136,6] 13 :=
  permutation_upper _ _ _ [304,80,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8617

theorem m9481_33 : Upper (D 1) (R 1) [304,80,136,33] 13 :=
  permutation_upper _ _ _ [304,80,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8622

theorem m9481_34 : Upper (D 1) (R 1) [304,80,136,34] 13 :=
  permutation_upper _ _ _ [304,80,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8629

theorem m9481_36 : Upper (D 1) (R 1) [304,80,136,36] 13 :=
  permutation_upper _ _ _ [304,80,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8636

theorem m9481_65 : Upper (D 1) (R 1) [304,80,136,65] 13 :=
  permutation_upper _ _ _ [304,80,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8639

theorem m9481_66 : Upper (D 1) (R 1) [304,80,136,66] 13 :=
  permutation_upper _ _ _ [304,80,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8643

theorem m9481_68 : Upper (D 1) (R 1) [304,80,136,68] 13 :=
  permutation_upper _ _ _ [304,80,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8647

theorem m9481_96 : Upper (D 1) (R 1) [304,80,136,96] 13 :=
  permutation_upper _ _ _ [304,80,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8651

theorem m9481_129 : Upper (D 1) (R 1) [304,80,136,129] 13 :=
  permutation_upper _ _ _ [304,80,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8653

theorem m9481_130 : Upper (D 1) (R 1) [304,80,136,130] 13 :=
  permutation_upper _ _ _ [304,80,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8657

def r9481 : Route 9 := (fun mask => (mask,id))

def c9481 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9481 : Upper (D 1) (R 1) [304,80,136] 13 := by
  apply FastRouting.sound _ _ [304,80,136] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r9481 c9481
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9481_3
  · exact m9481_5
  · exact m9481_6
  · exact m9481_33
  · exact m9481_34
  · exact m9481_36
  · exact m9481_65
  · exact m9481_66
  · exact m9481_68
  · exact m9481_96
  · exact m9481_129
  · exact m9481_130
  · exact u8660
  · exact u8661
  · exact u8662

theorem m9482_3 : Upper (D 1) (R 1) [304,80,160,3] 13 :=
  permutation_upper _ _ _ [304,80,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8595

theorem m9482_5 : Upper (D 1) (R 1) [304,80,160,5] 13 :=
  permutation_upper _ _ _ [304,80,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8605

theorem m9482_6 : Upper (D 1) (R 1) [304,80,160,6] 13 :=
  permutation_upper _ _ _ [304,80,10,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8618

theorem m9482_65 : Upper (D 1) (R 1) [304,80,160,65] 13 :=
  permutation_upper _ _ _ [304,80,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8640

theorem m9482_66 : Upper (D 1) (R 1) [304,80,160,66] 13 :=
  permutation_upper _ _ _ [304,80,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8644

theorem m9482_68 : Upper (D 1) (R 1) [304,80,160,68] 13 :=
  permutation_upper _ _ _ [304,80,72,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8648

theorem m9482_129 : Upper (D 1) (R 1) [304,80,160,129] 13 :=
  permutation_upper _ _ _ [304,80,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8654

theorem m9482_130 : Upper (D 1) (R 1) [304,80,160,130] 13 :=
  permutation_upper _ _ _ [304,80,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8658

theorem m9482_132 : Upper (D 1) (R 1) [304,80,160,132] 13 :=
  permutation_upper _ _ _ [304,80,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8661

def r9482 : Route 9 := (fun mask => (mask,id))

def c9482 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9482 : Upper (D 1) (R 1) [304,80,160] 13 := by
  apply FastRouting.sound _ _ [304,80,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9482 c9482
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9482_3
  · exact m9482_5
  · exact m9482_6
  · exact m9482_65
  · exact m9482_66
  · exact m9482_68
  · exact m9482_129
  · exact m9482_130
  · exact m9482_132
  · exact u8663

theorem m9483_3 : Upper (D 1) (R 1) [304,80,192,3] 13 :=
  permutation_upper _ _ _ [304,80,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8596

theorem m9483_5 : Upper (D 1) (R 1) [304,80,192,5] 13 :=
  permutation_upper _ _ _ [304,80,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8606

theorem m9483_6 : Upper (D 1) (R 1) [304,80,192,6] 13 :=
  permutation_upper _ _ _ [304,80,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8619

theorem m9483_33 : Upper (D 1) (R 1) [304,80,192,33] 13 :=
  permutation_upper _ _ _ [304,80,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8623

theorem m9483_34 : Upper (D 1) (R 1) [304,80,192,34] 13 :=
  permutation_upper _ _ _ [304,80,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8630

theorem m9483_36 : Upper (D 1) (R 1) [304,80,192,36] 13 :=
  permutation_upper _ _ _ [304,80,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8637

theorem m9483_129 : Upper (D 1) (R 1) [304,80,192,129] 13 :=
  permutation_upper _ _ _ [304,80,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8655

theorem m9483_130 : Upper (D 1) (R 1) [304,80,192,130] 13 :=
  permutation_upper _ _ _ [304,80,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8659

theorem m9483_132 : Upper (D 1) (R 1) [304,80,192,132] 13 :=
  permutation_upper _ _ _ [304,80,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8662

theorem m9483_160 : Upper (D 1) (R 1) [304,80,192,160] 13 :=
  permutation_upper _ _ _ [304,80,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8663

def r9483 : Route 9 := (fun mask => (mask,id))

def c9483 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 257 => 8 | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9483 : Upper (D 1) (R 1) [304,80,192] 13 := by
  apply FastRouting.sound _ _ [304,80,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r9483 c9483
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9483_3
  · exact m9483_5
  · exact m9483_6
  · exact m9483_33
  · exact m9483_34
  · exact m9483_36
  · exact m9483_129
  · exact m9483_130
  · exact m9483_132
  · exact m9483_160

def r9484 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9484 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9484 : Upper (D 1) (R 1) [304,192,3] 13 := by
  apply FastRouting.sound _ _ [304,192,3] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192] r9484 c9484
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8664
  · exact u8665
  · exact u8666
  · exact u8667
  · exact u8668
  · exact u8669
  · exact u8670
  · exact u8671

def r9485 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9485 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9485 : Upper (D 1) (R 1) [304,192,9] 13 := by
  apply FastRouting.sound _ _ [304,192,9] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192] r9485 c9485
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8672
  · exact u8673
  · exact u8674
  · exact u8675
  · exact u8676
  · exact u8677
  · exact u8678
  · exact u8679

theorem m9486_3 : Upper (D 1) (R 1) [304,192,10,3] 13 :=
  permutation_upper _ _ _ [304,192,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8664

theorem m9486_5 : Upper (D 1) (R 1) [304,192,10,5] 13 :=
  permutation_upper _ _ _ [304,192,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8672

def r9486 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9486 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9486 : Upper (D 1) (R 1) [304,192,10] 13 := by
  apply FastRouting.sound _ _ [304,192,10] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,65,66,68,80,192] r9486 c9486
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9486_3
  · exact m9486_5
  · exact u8680
  · exact u8681
  · exact u8682
  · exact u8683
  · exact u8684
  · exact u8685
  · exact u8686
  · exact u8687
  · exact u8688
  · exact u8689

def b9487 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 21 238 254 238 238 238 494), lower := (rows 305 194 21 8 16 32 64 128 256), losses := [] }

theorem u9487 : Upper (D 1) (R 1) [304,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9487
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9488_3 : Upper (D 1) (R 1) [304,192,18,3] 13 :=
  permutation_upper _ _ _ [304,192,3,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8665

theorem m9488_5 : Upper (D 1) (R 1) [304,192,18,5] 13 :=
  permutation_upper _ _ _ [304,192,9,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8673

theorem m9488_6 : Upper (D 1) (R 1) [304,192,18,6] 13 :=
  permutation_upper _ _ _ [304,192,10,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8682

theorem m9488_33 : Upper (D 1) (R 1) [304,192,18,33] 13 :=
  permutation_upper _ _ _ [304,192,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8690

def r9488 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9488 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9488 : Upper (D 1) (R 1) [304,192,18] 13 := by
  apply FastRouting.sound _ _ [304,192,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9488 c9488
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9488_3
  · exact m9488_5
  · exact m9488_6
  · exact m9488_33
  · exact u8694
  · exact u8695
  · exact u8696
  · exact u8697
  · exact u8698
  · exact u8699
  · exact u8700

theorem m9489_3 : Upper (D 1) (R 1) [304,192,24,3] 13 :=
  permutation_upper _ _ _ [304,192,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8666

theorem m9489_5 : Upper (D 1) (R 1) [304,192,24,5] 13 :=
  permutation_upper _ _ _ [304,192,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8674

theorem m9489_6 : Upper (D 1) (R 1) [304,192,24,6] 13 :=
  permutation_upper _ _ _ [304,192,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8683

theorem m9489_33 : Upper (D 1) (R 1) [304,192,24,33] 13 :=
  permutation_upper _ _ _ [304,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8691

theorem m9489_34 : Upper (D 1) (R 1) [304,192,24,34] 13 :=
  permutation_upper _ _ _ [304,192,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8695

def r9489 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9489 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9489 : Upper (D 1) (R 1) [304,192,24] 13 := by
  apply FastRouting.sound _ _ [304,192,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r9489 c9489
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9489_3
  · exact m9489_5
  · exact m9489_6
  · exact m9489_33
  · exact m9489_34
  · exact u8701
  · exact u8702
  · exact u8703
  · exact u8704
  · exact u8705
  · exact u8706

def b9490 : PairBound 9 := { available := 207, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 194 52 207 223 239 207 207 463), lower := (rows 305 194 52 8 16 32 64 128 256), losses := [] }

theorem u9490 : Upper (D 1) (R 1) [304,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9490
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9491_6 : Upper (D 1) (R 1) [304,192,65,6] 13 :=
  permutation_upper _ _ _ [304,192,10,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8685

theorem m9491_18 : Upper (D 1) (R 1) [304,192,65,18] 13 :=
  permutation_upper _ _ _ [304,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8696

theorem m9491_20 : Upper (D 1) (R 1) [304,192,65,20] 13 :=
  permutation_upper _ _ _ [304,192,24,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8702

theorem m9491_48 : Upper (D 1) (R 1) [304,192,65,48] 13 :=
  permutation_upper _ _ _ [304,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8707

def r9491 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9491 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9491 : Upper (D 1) (R 1) [304,192,65] 13 := by
  apply FastRouting.sound _ _ [304,192,65] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r9491 c9491
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9491_6
  · exact m9491_18
  · exact m9491_20
  · exact m9491_48
  · exact u8709
  · exact u8710
  · exact u8711

def b9492 : PairBound 9 := { available := 191, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 70 191 191 191 255 191 447), lower := (rows 305 194 70 8 16 32 64 128 256), losses := [] }

theorem u9492 : Upper (D 1) (R 1) [304,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9492
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9493_3 : Upper (D 1) (R 1) [304,192,72,3] 13 :=
  permutation_upper _ _ _ [304,192,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8669

theorem m9493_5 : Upper (D 1) (R 1) [304,192,72,5] 13 :=
  permutation_upper _ _ _ [304,192,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8677

theorem m9493_6 : Upper (D 1) (R 1) [304,192,72,6] 13 :=
  permutation_upper _ _ _ [304,192,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8687

theorem m9493_17 : Upper (D 1) (R 1) [304,192,72,17] 13 :=
  permutation_upper _ _ _ [304,192,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8692

theorem m9493_18 : Upper (D 1) (R 1) [304,192,72,18] 13 :=
  permutation_upper _ _ _ [304,192,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8698

theorem m9493_20 : Upper (D 1) (R 1) [304,192,72,20] 13 :=
  permutation_upper _ _ _ [304,192,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8704

theorem m9493_48 : Upper (D 1) (R 1) [304,192,72,48] 13 :=
  permutation_upper _ _ _ [304,192,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8708

theorem m9493_129 : Upper (D 1) (R 1) [304,192,72,129] 13 :=
  permutation_upper _ _ _ [304,192,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8710

theorem m9493_130 : Upper (D 1) (R 1) [304,192,72,130] 13 :=
  permutation_upper _ _ _ [304,192,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8712

def r9493 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9493 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9493 : Upper (D 1) (R 1) [304,192,72] 13 := by
  apply FastRouting.sound _ _ [304,192,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144] r9493 c9493
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9493_3
  · exact m9493_5
  · exact m9493_6
  · exact m9493_17
  · exact m9493_18
  · exact m9493_20
  · exact m9493_48
  · exact m9493_129
  · exact m9493_130
  · exact u8714
  · exact u8715

theorem m9494_3 : Upper (D 1) (R 1) [304,192,80,3] 13 :=
  permutation_upper _ _ _ [304,192,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8670

theorem m9494_5 : Upper (D 1) (R 1) [304,192,80,5] 13 :=
  permutation_upper _ _ _ [304,192,9,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8678

theorem m9494_6 : Upper (D 1) (R 1) [304,192,80,6] 13 :=
  permutation_upper _ _ _ [304,192,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8688

theorem m9494_33 : Upper (D 1) (R 1) [304,192,80,33] 13 :=
  permutation_upper _ _ _ [304,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8693

theorem m9494_34 : Upper (D 1) (R 1) [304,192,80,34] 13 :=
  permutation_upper _ _ _ [304,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8699

theorem m9494_36 : Upper (D 1) (R 1) [304,192,80,36] 13 :=
  permutation_upper _ _ _ [304,192,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8705

theorem m9494_129 : Upper (D 1) (R 1) [304,192,80,129] 13 :=
  permutation_upper _ _ _ [304,192,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8711

theorem m9494_130 : Upper (D 1) (R 1) [304,192,80,130] 13 :=
  permutation_upper _ _ _ [304,192,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8713

theorem m9494_132 : Upper (D 1) (R 1) [304,192,80,132] 13 :=
  permutation_upper _ _ _ [304,192,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8715

def r9494 : Route 9 := (fun mask => (mask,id))

def c9494 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 257 => 8 | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9494 : Upper (D 1) (R 1) [304,192,80] 13 := by
  apply FastRouting.sound _ _ [304,192,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r9494 c9494
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9494_3
  · exact m9494_5
  · exact m9494_6
  · exact m9494_33
  · exact m9494_34
  · exact m9494_36
  · exact m9494_129
  · exact m9494_130
  · exact m9494_132
  · exact u8716

def b9495 : PairBound 9 := { available := 63, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 194 196 63 63 63 127 191 319), lower := (rows 305 194 196 8 16 32 64 128 256), losses := [] }

theorem u9495 : Upper (D 1) (R 1) [304,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9495
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9496 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9496 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9496 : Upper (D 1) (R 1) [14,17] 13 := by
  apply FastRouting.sound _ _ [14,17] 13 (by decide) (choices 2) [18,34,48,96,258,272,288] r9496 c9496
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8717
  · exact u8718
  · exact u8719
  · exact u8720
  · exact u8721
  · exact u8722
  · exact u8723

def r9497 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9497 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9497 : Upper (D 1) (R 1) [14,48] 13 := by
  apply FastRouting.sound _ _ [14,48] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320] r9497 c9497
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8724
  · exact u8725
  · exact u8726
  · exact u8727
  · exact u8728
  · exact u8729
  · exact u8730
  · exact u8731
  · exact u8732
  · exact u8733
  · exact u8734
  · exact u8735

def r9498 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 130 => (18,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (48,(fun i => match i.val with | 4 => 7 | 7 => 4 | _ => i)) | 192 => (48,(fun i => match i.val with | 4 => 6 | 5 => 7 | 6 => 4 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9498 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9498 : Upper (D 1) (R 1) [14,257] 13 := by
  apply FastRouting.sound _ _ [14,257] 13 (by decide) (choices 2) [18,48] r9498 c9498
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u8736
  · exact u8737

def r9499 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9499 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9499 : Upper (D 1) (R 1) [14,272] 13 := by
  apply FastRouting.sound _ _ [14,272] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r9499 c9499
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8738
  · exact u8739
  · exact u8740
  · exact u8741
  · exact u8742
  · exact u8743
  · exact u8744

def r9500 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 384 => (288,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9500 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9500 : Upper (D 1) (R 1) [22,9] 13 := by
  apply FastRouting.sound _ _ [22,9] 13 (by decide) (choices 2) [18,34,48,96,258,272,288] r9500 c9500
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8745
  · exact u8746
  · exact u8747
  · exact u8748
  · exact u8749
  · exact u8750
  · exact u8751

def b9501 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 23 19 494 490 506 490 490 490 490), lower := (rows 23 19 4 8 16 32 64 128 256), losses := [] }

theorem u9501 : Upper (D 1) (R 1) [22,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9502 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 484, targets := 16 }], pairs := [(2,4)], upper := (rows 23 26 487 491 499 483 483 483 483), lower := (rows 23 26 4 8 16 32 64 128 256), losses := [] }

theorem u9502 : Upper (D 1) (R 1) [22,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9503 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9503 : Nat → Fin 9 := (fun _ => 0)

theorem u9503 : Upper (D 1) (R 1) [22,33] 13 := by
  apply FastRouting.sound _ _ [22,33] 13 (by decide) (choices 2) [10,18,24,34,40,48,66,72,80,96,192,258,264,272,288,320] r9503 c9503
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8752
  · exact u8753
  · exact u8754
  · exact u8755
  · exact u8756
  · exact u8757
  · exact u8758
  · exact u8759
  · exact u8760
  · exact u8761
  · exact u8762
  · exact u8763
  · exact u8764
  · exact u8765
  · exact u8766
  · exact u8767

def r9504 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9504 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9504 : Upper (D 1) (R 1) [22,40] 13 := by
  apply FastRouting.sound _ _ [22,40] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r9504 c9504
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8768
  · exact u8769
  · exact u8770
  · exact u8771
  · exact u8772
  · exact u8773
  · exact u8774
  · exact u8775
  · exact u8776
  · exact u8777
  · exact u8778
  · exact u8779
  · exact u8780
  · exact u8781
  · exact u8782
  · exact u8783

def b9505 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 492, targets := 16 }], pairs := [(2,4)], upper := (rows 23 50 495 491 507 491 491 491 491), lower := (rows 23 50 4 8 16 32 64 128 256), losses := [] }

theorem u9505 : Upper (D 1) (R 1) [22,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9506 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9506 : Nat → Fin 9 := (fun _ => 0)

theorem u9506 : Upper (D 1) (R 1) [22,96] 13 := by
  apply FastRouting.sound _ _ [22,96] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,96,129,130,136,144,160,257,258,264,272,288,384] r9506 c9506
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8784
  · exact u8785
  · exact u8786
  · exact u8787
  · exact u8788
  · exact u8789
  · exact u8790
  · exact u8791
  · exact u8792
  · exact u8793
  · exact u8794
  · exact u8795
  · exact u8796
  · exact u8797
  · exact u8798
  · exact u8799
  · exact u8800
  · exact u8801
  · exact u8802
  · exact u8803
  · exact u8804
  · exact u8805

def r9507 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 136 => (40,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9507 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9507 : Upper (D 1) (R 1) [22,257] 13 := by
  apply FastRouting.sound _ _ [22,257] 13 (by decide) (choices 2) [10,18,24,34,40,48,96] r9507 c9507
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8806
  · exact u8807
  · exact u8808
  · exact u8809
  · exact u8810
  · exact u8811
  · exact u8812

def r9508 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9508 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9508 : Upper (D 1) (R 1) [22,264] 13 := by
  apply FastRouting.sound _ _ [22,264] 13 (by decide) (choices 2) [3,17,18,33,34,48,96] r9508 c9508
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8813
  · exact u8814
  · exact u8815
  · exact u8816
  · exact u8817
  · exact u8818
  · exact u8819

def b9509 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 236, targets := 16 }], pairs := [(2,4)], upper := (rows 23 274 239 235 251 235 235 235 491), lower := (rows 23 274 4 8 16 32 64 128 256), losses := [] }

theorem u9509 : Upper (D 1) (R 1) [22,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9510 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9510 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9510 : Upper (D 1) (R 1) [22,288] 13 := by
  apply FastRouting.sound _ _ [22,288] 13 (by decide) (choices 2) [3,9,10,17,18,24,33,34,40,48,65,66,72,80,96,192] r9510 c9510
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8820
  · exact u8821
  · exact u8822
  · exact u8823
  · exact u8824
  · exact u8825
  · exact u8826
  · exact u8827
  · exact u8828
  · exact u8829
  · exact u8830
  · exact u8831
  · exact u8832
  · exact u8833
  · exact u8834
  · exact u8835

def b9511 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 29 19 486 490 498 482 482 482 482), lower := (rows 29 19 4 8 16 32 64 128 256), losses := [] }

theorem u9511 : Upper (D 1) (R 1) [28,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9512 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9512 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9512 : Upper (D 1) (R 1) [28,33] 13 := by
  apply FastRouting.sound _ _ [28,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192,258,272,288,320] r9512 c9512
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8836
  · exact u8837
  · exact u8838
  · exact u8839
  · exact u8840
  · exact u8841
  · exact u8842
  · exact u8843
  · exact u8844
  · exact u8845
  · exact u8846

def r9513 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9513 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9513 : Upper (D 1) (R 1) [28,48] 13 := by
  apply FastRouting.sound _ _ [28,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r9513 c9513
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8847
  · exact u8848
  · exact u8849
  · exact u8850
  · exact u8851
  · exact u8852
  · exact u8853
  · exact u8854
  · exact u8855
  · exact u8856
  · exact u8857

def r9514 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9514 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9514 : Upper (D 1) (R 1) [28,96] 13 := by
  apply FastRouting.sound _ _ [28,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160,257,258,272,288,384] r9514 c9514
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8858
  · exact u8859
  · exact u8860
  · exact u8861
  · exact u8862
  · exact u8863
  · exact u8864
  · exact u8865
  · exact u8866
  · exact u8867
  · exact u8868
  · exact u8869
  · exact u8870
  · exact u8871
  · exact u8872
  · exact u8873

def r9515 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 144 => (48,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9515 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9515 : Upper (D 1) (R 1) [28,257] 13 := by
  apply FastRouting.sound _ _ [28,257] 13 (by decide) (choices 2) [18,34,48,96] r9515 c9515
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8874
  · exact u8875
  · exact u8876
  · exact u8877

def r9516 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 129 => (33,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 130 => (34,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 192 => (96,(fun i => match i.val with | 5 => 7 | 7 => 5 | _ => i)) | _ => (mask,id))

def c9516 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 257 => 8 | 10 => 3 | 18 => 4 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9516 : Upper (D 1) (R 1) [28,272] 13 := by
  apply FastRouting.sound _ _ [28,272] 13 (by decide) (choices 2) [3,33,34,96] r9516 c9516
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8878
  · exact u8879
  · exact u8880
  · exact u8881

def r9517 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9517 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9517 : Upper (D 1) (R 1) [28,288] 13 := by
  apply FastRouting.sound _ _ [28,288] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192] r9517 c9517
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8882
  · exact u8883
  · exact u8884
  · exact u8885
  · exact u8886
  · exact u8887
  · exact u8888
  · exact u8889
  · exact u8890
  · exact u8891
  · exact u8892

def r9518 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9518 : Nat → Fin 9 := (fun _ => 0)

theorem u9518 : Upper (D 1) (R 1) [50,5] 13 := by
  apply FastRouting.sound _ _ [50,5] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192,258,264,272,320] r9518 c9518
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8893
  · exact u8894
  · exact u8895
  · exact u8896
  · exact u8897
  · exact u8898
  · exact u8899
  · exact u8900
  · exact u8901
  · exact u8902
  · exact u8903
  · exact u8904

def r9519 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9519 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9519 : Upper (D 1) (R 1) [50,12] 13 := by
  apply FastRouting.sound _ _ [50,12] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192,257,258,272,320] r9519 c9519
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8905
  · exact u8906
  · exact u8907
  · exact u8908
  · exact u8909
  · exact u8910
  · exact u8911
  · exact u8912
  · exact u8913
  · exact u8914
  · exact u8915
  · exact u8916

def b9520 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 51 19 494 494 510 494 494 494 494), lower := (rows 51 19 4 8 16 32 64 128 256), losses := [] }

theorem u9520 : Upper (D 1) (R 1) [50,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9521 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 51 22 495 491 507 491 491 491 491), lower := (rows 51 22 4 8 16 32 64 128 256), losses := [] }

theorem u9521 : Upper (D 1) (R 1) [50,20] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9521
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9522 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 51 50 463 463 479 495 463 463 463), lower := (rows 51 50 4 8 16 32 64 128 256), losses := [] }

theorem u9522 : Upper (D 1) (R 1) [50,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9523 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9523 : Nat → Fin 9 := (fun _ => 0)

theorem u9523 : Upper (D 1) (R 1) [50,65] 13 := by
  apply FastRouting.sound _ _ [50,65] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,130,136,144,192,258,264,272,320,384] r9523 c9523
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8917
  · exact u8918
  · exact u8919
  · exact u8920
  · exact u8921
  · exact u8922
  · exact u8923
  · exact u8924
  · exact u8925
  · exact u8926
  · exact u8927
  · exact u8928
  · exact u8929
  · exact u8930
  · exact u8931
  · exact u8932

def r9524 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9524 : Nat → Fin 9 := (fun _ => 0)

theorem u9524 : Upper (D 1) (R 1) [50,68] 13 := by
  apply FastRouting.sound _ _ [50,68] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192,257,258,264,272,320,384] r9524 c9524
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8933
  · exact u8934
  · exact u8935
  · exact u8936
  · exact u8937
  · exact u8938
  · exact u8939
  · exact u8940
  · exact u8941
  · exact u8942
  · exact u8943
  · exact u8944
  · exact u8945
  · exact u8946
  · exact u8947
  · exact u8948
  · exact u8949
  · exact u8950
  · exact u8951
  · exact u8952
  · exact u8953
  · exact u8954

def b9525 : PairBound 9 := { available := 495, camps := [{ cop := 0, region := 460, targets := 16 }], pairs := [(2,4)], upper := (rows 51 82 495 495 511 495 495 495 495), lower := (rows 51 82 4 8 16 32 64 128 256), losses := [] }

theorem u9525 : Upper (D 1) (R 1) [50,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9526 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9526 : Nat → Fin 9 := (fun _ => 0)

theorem u9526 : Upper (D 1) (R 1) [50,192] 13 := by
  apply FastRouting.sound _ _ [50,192] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192,257,258,264,272,320] r9526 c9526
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8955
  · exact u8956
  · exact u8957
  · exact u8958
  · exact u8959
  · exact u8960
  · exact u8961
  · exact u8962
  · exact u8963
  · exact u8964
  · exact u8965
  · exact u8966
  · exact u8967
  · exact u8968
  · exact u8969
  · exact u8970
  · exact u8971

def r9527 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9527 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9527 : Upper (D 1) (R 1) [50,257] 13 := by
  apply FastRouting.sound _ _ [50,257] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192] r9527 c9527
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8972
  · exact u8973
  · exact u8974
  · exact u8975
  · exact u8976
  · exact u8977
  · exact u8978
  · exact u8979

def r9528 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9528 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9528 : Upper (D 1) (R 1) [50,260] 13 := by
  apply FastRouting.sound _ _ [50,260] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192] r9528 c9528
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8980
  · exact u8981
  · exact u8982
  · exact u8983
  · exact u8984
  · exact u8985
  · exact u8986
  · exact u8987
  · exact u8988
  · exact u8989
  · exact u8990
  · exact u8991

def b9529 : PairBound 9 := { available := 239, camps := [{ cop := 0, region := 204, targets := 16 }], pairs := [(2,4)], upper := (rows 51 274 239 239 255 239 239 239 495), lower := (rows 51 274 4 8 16 32 64 128 256), losses := [] }

theorem u9529 : Upper (D 1) (R 1) [50,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9530 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9530 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9530 : Upper (D 1) (R 1) [50,320] 13 := by
  apply FastRouting.sound _ _ [50,320] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,129,130,136,144,192] r9530 c9530
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8992
  · exact u8993
  · exact u8994
  · exact u8995
  · exact u8996
  · exact u8997
  · exact u8998
  · exact u8999
  · exact u9000
  · exact u9001
  · exact u9002
  · exact u9003
  · exact u9004
  · exact u9005
  · exact u9006
  · exact u9007

def r9531 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9531 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9531 : Upper (D 1) (R 1) [52,9] 13 := by
  apply FastRouting.sound _ _ [52,9] 13 (by decide) (choices 2) [18,48,66,80,192,258,272,320] r9531 c9531
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9008
  · exact u9009
  · exact u9010
  · exact u9011
  · exact u9012
  · exact u9013
  · exact u9014
  · exact u9015

def b9532 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 53 19 494 490 506 490 490 490 490), lower := (rows 53 19 4 8 16 32 64 128 256), losses := [] }

theorem u9532 : Upper (D 1) (R 1) [52,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9533 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9533 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 17 => 4 | 10 => 3 | 18 => 4 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9533 : Upper (D 1) (R 1) [52,24] 13 := by
  apply FastRouting.sound _ _ [52,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r9533 c9533
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9016
  · exact u9017
  · exact u9018
  · exact u9019
  · exact u9020
  · exact u9021
  · exact u9022
  · exact u9023
  · exact u9024
  · exact u9025
  · exact u9026

def b9534 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 53 50 463 459 475 491 459 459 459), lower := (rows 53 50 4 8 16 32 64 128 256), losses := [] }

theorem u9534 : Upper (D 1) (R 1) [52,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9535 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9535 : Nat → Fin 9 := (fun _ => 0)

theorem u9535 : Upper (D 1) (R 1) [52,65] 13 := by
  apply FastRouting.sound _ _ [52,65] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,130,136,144,192,258,264,272,320,384] r9535 c9535
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9027
  · exact u9028
  · exact u9029
  · exact u9030
  · exact u9031
  · exact u9032
  · exact u9033
  · exact u9034
  · exact u9035
  · exact u9036
  · exact u9037
  · exact u9038
  · exact u9039
  · exact u9040
  · exact u9041
  · exact u9042

def r9536 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9536 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9536 : Upper (D 1) (R 1) [52,72] 13 := by
  apply FastRouting.sound _ _ [52,72] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192,257,258,272,320,384] r9536 c9536
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9043
  · exact u9044
  · exact u9045
  · exact u9046
  · exact u9047
  · exact u9048
  · exact u9049
  · exact u9050
  · exact u9051
  · exact u9052
  · exact u9053
  · exact u9054
  · exact u9055
  · exact u9056
  · exact u9057
  · exact u9058

def r9537 : Route 9 := (fun mask => (mask,id))

def c9537 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 24 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9537 : Upper (D 1) (R 1) [52,80] 13 := by
  apply FastRouting.sound _ _ [52,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192,257,258,264,288,320,384] r9537 c9537
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9059
  · exact u9060
  · exact u9061
  · exact u9062
  · exact u9063
  · exact u9064
  · exact u9065
  · exact u9066
  · exact u9067
  · exact u9068
  · exact u9069
  · exact u9070
  · exact u9071
  · exact u9072
  · exact u9073
  · exact u9074
  · exact u9075
  · exact u9076
  · exact u9077
  · exact u9078
  · exact u9079

def r9538 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9538 : Nat → Fin 9 := (fun _ => 0)

theorem u9538 : Upper (D 1) (R 1) [52,192] 13 := by
  apply FastRouting.sound _ _ [52,192] 13 (by decide) (choices 2) [3,9,10,17,18,24,48,65,66,72,80,192,257,258,264,272,320] r9538 c9538
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9080
  · exact u9081
  · exact u9082
  · exact u9083
  · exact u9084
  · exact u9085
  · exact u9086
  · exact u9087
  · exact u9088
  · exact u9089
  · exact u9090
  · exact u9091
  · exact u9092
  · exact u9093
  · exact u9094
  · exact u9095
  · exact u9096

def r9539 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 40 => (24,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9539 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 264 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9539 : Upper (D 1) (R 1) [52,257] 13 := by
  apply FastRouting.sound _ _ [52,257] 13 (by decide) (choices 2) [10,18,24,48,66,72,80,192] r9539 c9539
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u9097
  · exact u9098
  · exact u9099
  · exact u9100
  · exact u9101
  · exact u9102
  · exact u9103
  · exact u9104

#print axioms u9539
end Delivery.IrregularNine14.P01
