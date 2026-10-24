import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0111
import IrregularNine14P01C0112
import IrregularNine14P01C0113
import IrregularNine14P01C0114
import IrregularNine14P01C0115

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9000 : PairBound 9 := { available := 189, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 70 189 189 189 253 189 445), lower := (rows 51 322 70 8 16 32 64 128 256), losses := [] }

theorem u9000 : Upper (D 1) (R 1) [50,320,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9000
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9001_3 : Upper (D 1) (R 1) [50,320,72,3] 13 :=
  permutation_upper _ _ _ [50,320,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6663

theorem m9001_5 : Upper (D 1) (R 1) [50,320,72,5] 13 :=
  permutation_upper _ _ _ [50,320,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6673

theorem m9001_6 : Upper (D 1) (R 1) [50,320,72,6] 13 :=
  permutation_upper _ _ _ [50,320,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6683

theorem m9001_17 : Upper (D 1) (R 1) [50,320,72,17] 13 :=
  permutation_upper _ _ _ [50,320,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6690

theorem m9001_18 : Upper (D 1) (R 1) [50,320,72,18] 13 :=
  permutation_upper _ _ _ [50,320,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6698

theorem m9001_20 : Upper (D 1) (R 1) [50,320,72,20] 13 :=
  permutation_upper _ _ _ [50,320,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6707

theorem m9001_48 : Upper (D 1) (R 1) [50,320,72,48] 13 :=
  permutation_upper _ _ _ [50,320,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6715

def r9001 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9001 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9001 : Upper (D 1) (R 1) [50,320,72] 13 := by
  apply FastRouting.sound _ _ [50,320,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144] r9001 c9001
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9001_3
  · exact m9001_5
  · exact m9001_6
  · exact m9001_17
  · exact m9001_18
  · exact m9001_20
  · exact m9001_48
  · exact u6726
  · exact u6727
  · exact u6728
  · exact u6729

theorem m9002_3 : Upper (D 1) (R 1) [50,320,80,3] 13 :=
  permutation_upper _ _ _ [50,320,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6664

theorem m9002_5 : Upper (D 1) (R 1) [50,320,80,5] 13 :=
  permutation_upper _ _ _ [50,320,9,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6674

theorem m9002_6 : Upper (D 1) (R 1) [50,320,80,6] 13 :=
  permutation_upper _ _ _ [50,320,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6684

theorem m9002_33 : Upper (D 1) (R 1) [50,320,80,33] 13 :=
  permutation_upper _ _ _ [50,320,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6691

theorem m9002_34 : Upper (D 1) (R 1) [50,320,80,34] 13 :=
  permutation_upper _ _ _ [50,320,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6699

theorem m9002_36 : Upper (D 1) (R 1) [50,320,80,36] 13 :=
  permutation_upper _ _ _ [50,320,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6708

def r9002 : Route 9 := (fun mask => (mask,id))

def c9002 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 257 => 8 | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9002 : Upper (D 1) (R 1) [50,320,80] 13 := by
  apply FastRouting.sound _ _ [50,320,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r9002 c9002
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9002_3
  · exact m9002_5
  · exact m9002_6
  · exact m9002_33
  · exact m9002_34
  · exact m9002_36
  · exact u6730
  · exact u6731
  · exact u6732
  · exact u6733

theorem m9003_6 : Upper (D 1) (R 1) [50,320,129,6] 13 :=
  permutation_upper _ _ _ [50,320,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6685

theorem m9003_18 : Upper (D 1) (R 1) [50,320,129,18] 13 :=
  permutation_upper _ _ _ [50,320,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6700

theorem m9003_20 : Upper (D 1) (R 1) [50,320,129,20] 13 :=
  permutation_upper _ _ _ [50,320,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6709

theorem m9003_48 : Upper (D 1) (R 1) [50,320,129,48] 13 :=
  permutation_upper _ _ _ [50,320,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6716

theorem m9003_66 : Upper (D 1) (R 1) [50,320,129,66] 13 :=
  permutation_upper _ _ _ [50,320,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6723

theorem m9003_68 : Upper (D 1) (R 1) [50,320,129,68] 13 :=
  permutation_upper _ _ _ [50,320,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6726

theorem m9003_80 : Upper (D 1) (R 1) [50,320,129,80] 13 :=
  permutation_upper _ _ _ [50,320,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6730

def r9003 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9003 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9003 : Upper (D 1) (R 1) [50,320,129] 13 := by
  apply FastRouting.sound _ _ [50,320,129] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r9003 c9003
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9003_6
  · exact m9003_18
  · exact m9003_20
  · exact m9003_48
  · exact m9003_66
  · exact m9003_68
  · exact m9003_80
  · exact u6734
  · exact u6735
  · exact u6736
  · exact u6737

theorem m9004_5 : Upper (D 1) (R 1) [50,320,130,5] 13 :=
  permutation_upper _ _ _ [50,320,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6675

theorem m9004_17 : Upper (D 1) (R 1) [50,320,130,17] 13 :=
  permutation_upper _ _ _ [50,320,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6692

theorem m9004_20 : Upper (D 1) (R 1) [50,320,130,20] 13 :=
  permutation_upper _ _ _ [50,320,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6710

theorem m9004_48 : Upper (D 1) (R 1) [50,320,130,48] 13 :=
  permutation_upper _ _ _ [50,320,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6717

theorem m9004_65 : Upper (D 1) (R 1) [50,320,130,65] 13 :=
  permutation_upper _ _ _ [50,320,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6720

theorem m9004_68 : Upper (D 1) (R 1) [50,320,130,68] 13 :=
  permutation_upper _ _ _ [50,320,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6727

theorem m9004_80 : Upper (D 1) (R 1) [50,320,130,80] 13 :=
  permutation_upper _ _ _ [50,320,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6731

theorem m9004_129 : Upper (D 1) (R 1) [50,320,130,129] 13 :=
  permutation_upper _ _ _ [50,320,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6734

def r9004 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9004 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9004 : Upper (D 1) (R 1) [50,320,130] 13 := by
  apply FastRouting.sound _ _ [50,320,130] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,129,132,144,192] r9004 c9004
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9004_5
  · exact m9004_17
  · exact m9004_20
  · exact m9004_48
  · exact m9004_65
  · exact m9004_68
  · exact m9004_80
  · exact m9004_129
  · exact u6738
  · exact u6739
  · exact u6740

theorem m9005_3 : Upper (D 1) (R 1) [50,320,136,3] 13 :=
  permutation_upper _ _ _ [50,320,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6665

theorem m9005_5 : Upper (D 1) (R 1) [50,320,136,5] 13 :=
  permutation_upper _ _ _ [50,320,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6676

theorem m9005_6 : Upper (D 1) (R 1) [50,320,136,6] 13 :=
  permutation_upper _ _ _ [50,320,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6686

theorem m9005_17 : Upper (D 1) (R 1) [50,320,136,17] 13 :=
  permutation_upper _ _ _ [50,320,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6693

theorem m9005_18 : Upper (D 1) (R 1) [50,320,136,18] 13 :=
  permutation_upper _ _ _ [50,320,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6701

theorem m9005_20 : Upper (D 1) (R 1) [50,320,136,20] 13 :=
  permutation_upper _ _ _ [50,320,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6711

theorem m9005_48 : Upper (D 1) (R 1) [50,320,136,48] 13 :=
  permutation_upper _ _ _ [50,320,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6718

theorem m9005_65 : Upper (D 1) (R 1) [50,320,136,65] 13 :=
  permutation_upper _ _ _ [50,320,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6721

theorem m9005_66 : Upper (D 1) (R 1) [50,320,136,66] 13 :=
  permutation_upper _ _ _ [50,320,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6724

theorem m9005_68 : Upper (D 1) (R 1) [50,320,136,68] 13 :=
  permutation_upper _ _ _ [50,320,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6728

theorem m9005_80 : Upper (D 1) (R 1) [50,320,136,80] 13 :=
  permutation_upper _ _ _ [50,320,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6732

theorem m9005_129 : Upper (D 1) (R 1) [50,320,136,129] 13 :=
  permutation_upper _ _ _ [50,320,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6735

theorem m9005_130 : Upper (D 1) (R 1) [50,320,136,130] 13 :=
  permutation_upper _ _ _ [50,320,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6738

def r9005 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9005 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9005 : Upper (D 1) (R 1) [50,320,136] 13 := by
  apply FastRouting.sound _ _ [50,320,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,65,66,68,80,129,130,132,144,192] r9005 c9005
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9005_3
  · exact m9005_5
  · exact m9005_6
  · exact m9005_17
  · exact m9005_18
  · exact m9005_20
  · exact m9005_48
  · exact m9005_65
  · exact m9005_66
  · exact m9005_68
  · exact m9005_80
  · exact m9005_129
  · exact m9005_130
  · exact u6741
  · exact u6742
  · exact u6743

theorem m9006_3 : Upper (D 1) (R 1) [50,320,144,3] 13 :=
  permutation_upper _ _ _ [50,320,3,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6666

theorem m9006_5 : Upper (D 1) (R 1) [50,320,144,5] 13 :=
  permutation_upper _ _ _ [50,320,9,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6677

theorem m9006_6 : Upper (D 1) (R 1) [50,320,144,6] 13 :=
  permutation_upper _ _ _ [50,320,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6687

theorem m9006_33 : Upper (D 1) (R 1) [50,320,144,33] 13 :=
  permutation_upper _ _ _ [50,320,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6694

theorem m9006_34 : Upper (D 1) (R 1) [50,320,144,34] 13 :=
  permutation_upper _ _ _ [50,320,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6702

theorem m9006_36 : Upper (D 1) (R 1) [50,320,144,36] 13 :=
  permutation_upper _ _ _ [50,320,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6712

theorem m9006_65 : Upper (D 1) (R 1) [50,320,144,65] 13 :=
  permutation_upper _ _ _ [50,320,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6722

theorem m9006_66 : Upper (D 1) (R 1) [50,320,144,66] 13 :=
  permutation_upper _ _ _ [50,320,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6725

theorem m9006_68 : Upper (D 1) (R 1) [50,320,144,68] 13 :=
  permutation_upper _ _ _ [50,320,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6729

theorem m9006_96 : Upper (D 1) (R 1) [50,320,144,96] 13 :=
  permutation_upper _ _ _ [50,320,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6733

theorem m9006_129 : Upper (D 1) (R 1) [50,320,144,129] 13 :=
  permutation_upper _ _ _ [50,320,129,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6736

theorem m9006_130 : Upper (D 1) (R 1) [50,320,144,130] 13 :=
  permutation_upper _ _ _ [50,320,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6739

theorem m9006_132 : Upper (D 1) (R 1) [50,320,144,132] 13 :=
  permutation_upper _ _ _ [50,320,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6742

def r9006 : Route 9 := (fun mask => (mask,id))

def c9006 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9006 : Upper (D 1) (R 1) [50,320,144] 13 := by
  apply FastRouting.sound _ _ [50,320,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r9006 c9006
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9006_3
  · exact m9006_5
  · exact m9006_6
  · exact m9006_33
  · exact m9006_34
  · exact m9006_36
  · exact m9006_65
  · exact m9006_66
  · exact m9006_68
  · exact m9006_96
  · exact m9006_129
  · exact m9006_130
  · exact m9006_132
  · exact u6744
  · exact u6745

theorem m9007_3 : Upper (D 1) (R 1) [50,320,192,3] 13 :=
  permutation_upper _ _ _ [50,320,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6667

theorem m9007_5 : Upper (D 1) (R 1) [50,320,192,5] 13 :=
  permutation_upper _ _ _ [50,320,9,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6678

theorem m9007_6 : Upper (D 1) (R 1) [50,320,192,6] 13 :=
  permutation_upper _ _ _ [50,320,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6688

theorem m9007_17 : Upper (D 1) (R 1) [50,320,192,17] 13 :=
  permutation_upper _ _ _ [50,320,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6695

theorem m9007_18 : Upper (D 1) (R 1) [50,320,192,18] 13 :=
  permutation_upper _ _ _ [50,320,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6703

theorem m9007_20 : Upper (D 1) (R 1) [50,320,192,20] 13 :=
  permutation_upper _ _ _ [50,320,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6713

theorem m9007_48 : Upper (D 1) (R 1) [50,320,192,48] 13 :=
  permutation_upper _ _ _ [50,320,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6719

theorem m9007_129 : Upper (D 1) (R 1) [50,320,192,129] 13 :=
  permutation_upper _ _ _ [50,320,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6737

theorem m9007_130 : Upper (D 1) (R 1) [50,320,192,130] 13 :=
  permutation_upper _ _ _ [50,320,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6740

theorem m9007_132 : Upper (D 1) (R 1) [50,320,192,132] 13 :=
  permutation_upper _ _ _ [50,320,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6743

theorem m9007_144 : Upper (D 1) (R 1) [50,320,192,144] 13 :=
  permutation_upper _ _ _ [50,320,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6745

def r9007 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9007 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9007 : Upper (D 1) (R 1) [50,320,192] 13 := by
  apply FastRouting.sound _ _ [50,320,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144] r9007 c9007
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9007_3
  · exact m9007_5
  · exact m9007_6
  · exact m9007_17
  · exact m9007_18
  · exact m9007_20
  · exact m9007_48
  · exact m9007_129
  · exact m9007_130
  · exact m9007_132
  · exact m9007_144

def b9008 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 11 22 490 498 482 482 482 482), lower := (rows 53 11 22 8 16 32 64 128 256), losses := [] }

theorem u9008 : Upper (D 1) (R 1) [52,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9008
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9009 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 11 52 458 466 482 450 450 450), lower := (rows 53 11 52 8 16 32 64 128 256), losses := [] }

theorem u9009 : Upper (D 1) (R 1) [52,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9009
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9010 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9010 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9010 : Upper (D 1) (R 1) [52,9,66] 13 := by
  apply FastRouting.sound _ _ [52,9,66] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9010 c9010
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6746
  · exact u6747
  · exact u6748
  · exact u6749
  · exact u6750
  · exact u6751
  · exact u6752
  · exact u6753
  · exact u6754
  · exact u6755
  · exact u6756

def b9011 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 11 84 490 498 482 482 482 482), lower := (rows 53 11 84 8 16 32 64 128 256), losses := [] }

theorem u9011 : Upper (D 1) (R 1) [52,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9011
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9012 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9012 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9012 : Upper (D 1) (R 1) [52,9,192] 13 := by
  apply FastRouting.sound _ _ [52,9,192] 13 (by decide) (choices 2) [18,48,66,80,192,258,272,320] r9012 c9012
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6757
  · exact u6758
  · exact u6759
  · exact u6760
  · exact u6761
  · exact u6762
  · exact u6763
  · exact u6764

def r9013 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9013 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9013 : Upper (D 1) (R 1) [52,9,258] 13 := by
  apply FastRouting.sound _ _ [52,9,258] 13 (by decide) (choices 2) [18,48,66,80,192] r9013 c9013
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u6765
  · exact u6766
  · exact u6767
  · exact u6768
  · exact u6769

def b9014 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 11 276 234 242 226 226 226 482), lower := (rows 53 11 276 8 16 32 64 128 256), losses := [] }

theorem u9014 : Upper (D 1) (R 1) [52,9,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9014
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9015 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9015 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9015 : Upper (D 1) (R 1) [52,9,320] 13 := by
  apply FastRouting.sound _ _ [52,9,320] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9015 c9015
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6770
  · exact u6771
  · exact u6772
  · exact u6773
  · exact u6774
  · exact u6775
  · exact u6776

def b9016 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 53 26 7 490 498 482 482 482 482), lower := (rows 53 26 7 8 16 32 64 128 256), losses := [] }

theorem u9016 : Upper (D 1) (R 1) [52,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9016
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9017 : PairBound 9 := { available := 450, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 26 37 458 466 482 450 450 450), lower := (rows 53 26 37 8 16 32 64 128 256), losses := [] }

theorem u9017 : Upper (D 1) (R 1) [52,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9017
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9018 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 38 459 467 483 451 451 451), lower := (rows 53 26 38 8 16 32 64 128 256), losses := [] }

theorem u9018 : Upper (D 1) (R 1) [52,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9018
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9019 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 488, targets := 16 }], pairs := [(3,4)], upper := (rows 53 26 69 490 498 482 482 482 482), lower := (rows 53 26 69 8 16 32 64 128 256), losses := [] }

theorem u9019 : Upper (D 1) (R 1) [52,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9019
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9020 : Route 9 := (fun mask => (mask,id))

def c9020 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9020 : Upper (D 1) (R 1) [52,24,66] 13 := by
  apply FastRouting.sound _ _ [52,24,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r9020 c9020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6777
  · exact u6778
  · exact u6779
  · exact u6780
  · exact u6781
  · exact u6782
  · exact u6783
  · exact u6784
  · exact u6785
  · exact u6786
  · exact u6787
  · exact u6788
  · exact u6789
  · exact u6790
  · exact u6791

def b9021 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 100 459 467 483 451 451 451), lower := (rows 53 26 100 8 16 32 64 128 256), losses := [] }

theorem u9021 : Upper (D 1) (R 1) [52,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9021
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9022 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9022 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 6 => 2 | 18 => 4 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u9022 : Upper (D 1) (R 1) [52,24,192] 13 := by
  apply FastRouting.sound _ _ [52,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r9022 c9022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6792
  · exact u6793
  · exact u6794
  · exact u6795
  · exact u6796
  · exact u6797
  · exact u6798
  · exact u6799
  · exact u6800
  · exact u6801
  · exact u6802

def b9023 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 53 26 261 234 242 226 226 226 482), lower := (rows 53 26 261 8 16 32 64 128 256), losses := [] }

theorem u9023 : Upper (D 1) (R 1) [52,24,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9023
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9024 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9024 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9024 : Upper (D 1) (R 1) [52,24,258] 13 := by
  apply FastRouting.sound _ _ [52,24,258] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9024 c9024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6803
  · exact u6804
  · exact u6805
  · exact u6806
  · exact u6807
  · exact u6808
  · exact u6809

def b9025 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 26 292 203 211 227 195 195 451), lower := (rows 53 26 292 8 16 32 64 128 256), losses := [] }

theorem u9025 : Upper (D 1) (R 1) [52,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9025
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9026 : Route 9 := (fun mask => (mask,id))

def c9026 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9026 : Upper (D 1) (R 1) [52,24,320] 13 := by
  apply FastRouting.sound _ _ [52,24,320] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9026 c9026
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6810
  · exact u6811
  · exact u6812
  · exact u6813
  · exact u6814
  · exact u6815
  · exact u6816
  · exact u6817
  · exact u6818
  · exact u6819

def r9027 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9027 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9027 : Upper (D 1) (R 1) [52,65,10] 13 := by
  apply FastRouting.sound _ _ [52,65,10] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9027 c9027
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6820
  · exact u6821
  · exact u6822
  · exact u6823
  · exact u6824
  · exact u6825
  · exact u6826
  · exact u6827
  · exact u6828
  · exact u6829
  · exact u6830

def b9028 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 22 490 506 490 490 490 490), lower := (rows 53 67 22 8 16 32 64 128 256), losses := [] }

theorem u9028 : Upper (D 1) (R 1) [52,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9028
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9029 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 450, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 28 490 498 482 482 482 482), lower := (rows 53 67 28 8 16 32 64 128 256), losses := [] }

theorem u9029 : Upper (D 1) (R 1) [52,65,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9029
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9030 : PairBound 9 := { available := 458, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 67 52 458 474 490 458 458 458), lower := (rows 53 67 52 8 16 32 64 128 256), losses := [] }

theorem u9030 : Upper (D 1) (R 1) [52,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9030
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9031 : PairBound 9 := { available := 442, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 67 70 442 442 442 506 442 442), lower := (rows 53 67 70 8 16 32 64 128 256), losses := [] }

theorem u9031 : Upper (D 1) (R 1) [52,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9031
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9032 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 53 67 76 442 434 434 498 434 434), lower := (rows 53 67 76 8 16 32 64 128 256), losses := [] }

theorem u9032 : Upper (D 1) (R 1) [52,65,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9032
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9033 : PairBound 9 := { available := 426, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 84 426 442 426 490 426 426), lower := (rows 53 67 84 8 16 32 64 128 256), losses := [] }

theorem u9033 : Upper (D 1) (R 1) [52,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9033
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9034 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9034 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9034 : Upper (D 1) (R 1) [52,65,130] 13 := by
  apply FastRouting.sound _ _ [52,65,130] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9034 c9034
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6831
  · exact u6832
  · exact u6833
  · exact u6834
  · exact u6835
  · exact u6836
  · exact u6837
  · exact u6838
  · exact u6839
  · exact u6840
  · exact u6841

def r9035 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9035 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9035 : Upper (D 1) (R 1) [52,65,136] 13 := by
  apply FastRouting.sound _ _ [52,65,136] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9035 c9035
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6842
  · exact u6843
  · exact u6844
  · exact u6845
  · exact u6846
  · exact u6847
  · exact u6848
  · exact u6849
  · exact u6850
  · exact u6851
  · exact u6852

def b9036 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 148 490 506 490 490 490 490), lower := (rows 53 67 148 8 16 32 64 128 256), losses := [] }

theorem u9036 : Upper (D 1) (R 1) [52,65,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9036
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9037 : PairBound 9 := { available := 442, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 53 67 196 442 442 442 506 442 442), lower := (rows 53 67 196 8 16 32 64 128 256), losses := [] }

theorem u9037 : Upper (D 1) (R 1) [52,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9037
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9038 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9038 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9038 : Upper (D 1) (R 1) [52,65,258] 13 := by
  apply FastRouting.sound _ _ [52,65,258] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9038 c9038
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6853
  · exact u6854
  · exact u6855
  · exact u6856
  · exact u6857
  · exact u6858
  · exact u6859

def r9039 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9039 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9039 : Upper (D 1) (R 1) [52,65,264] 13 := by
  apply FastRouting.sound _ _ [52,65,264] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9039 c9039
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6860
  · exact u6861
  · exact u6862
  · exact u6863
  · exact u6864
  · exact u6865
  · exact u6866

def b9040 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 67 276 234 250 234 234 234 490), lower := (rows 53 67 276 8 16 32 64 128 256), losses := [] }

theorem u9040 : Upper (D 1) (R 1) [52,65,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9040
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9041 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 53 67 324 186 186 186 250 186 442), lower := (rows 53 67 324 8 16 32 64 128 256), losses := [] }

theorem u9041 : Upper (D 1) (R 1) [52,65,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9041
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9042 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9042 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9042 : Upper (D 1) (R 1) [52,65,384] 13 := by
  apply FastRouting.sound _ _ [52,65,384] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9042 c9042
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6867
  · exact u6868
  · exact u6869
  · exact u6870
  · exact u6871
  · exact u6872
  · exact u6873

def r9043 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9043 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9043 : Upper (D 1) (R 1) [52,72,3] 13 := by
  apply FastRouting.sound _ _ [52,72,3] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9043 c9043
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6874
  · exact u6875
  · exact u6876
  · exact u6877
  · exact u6878
  · exact u6879
  · exact u6880
  · exact u6881
  · exact u6882
  · exact u6883
  · exact u6884

def b9044 : PairBound 9 := { available := 482, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 21 490 498 482 482 482 482), lower := (rows 53 74 21 8 16 32 64 128 256), losses := [] }

theorem u9044 : Upper (D 1) (R 1) [52,72,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9044
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9045 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 22 491 499 483 483 483 483), lower := (rows 53 74 22 8 16 32 64 128 256), losses := [] }

theorem u9045 : Upper (D 1) (R 1) [52,72,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9045
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9046 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 53 74 52 459 467 483 451 451 451), lower := (rows 53 74 52 8 16 32 64 128 256), losses := [] }

theorem u9046 : Upper (D 1) (R 1) [52,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9046
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9047 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 53 74 69 442 434 434 498 434 434), lower := (rows 53 74 69 8 16 32 64 128 256), losses := [] }

theorem u9047 : Upper (D 1) (R 1) [52,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9047
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9048 : PairBound 9 := { available := 435, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 53 74 70 443 435 435 499 435 435), lower := (rows 53 74 70 8 16 32 64 128 256), losses := [] }

theorem u9048 : Upper (D 1) (R 1) [52,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9048
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9049 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 84 427 435 419 483 419 419), lower := (rows 53 74 84 8 16 32 64 128 256), losses := [] }

theorem u9049 : Upper (D 1) (R 1) [52,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9049
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9050 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9050 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9050 : Upper (D 1) (R 1) [52,72,129] 13 := by
  apply FastRouting.sound _ _ [52,72,129] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r9050 c9050
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6885
  · exact u6886
  · exact u6887
  · exact u6888
  · exact u6889
  · exact u6890
  · exact u6891
  · exact u6892
  · exact u6893
  · exact u6894
  · exact u6895

def r9051 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9051 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9051 : Upper (D 1) (R 1) [52,72,130] 13 := by
  apply FastRouting.sound _ _ [52,72,130] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192,257,258,272,320,384] r9051 c9051
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6896
  · exact u6897
  · exact u6898
  · exact u6899
  · exact u6900
  · exact u6901
  · exact u6902
  · exact u6903
  · exact u6904
  · exact u6905
  · exact u6906
  · exact u6907
  · exact u6908
  · exact u6909
  · exact u6910
  · exact u6911

def b9052 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 458, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 148 491 499 483 483 483 483), lower := (rows 53 74 148 8 16 32 64 128 256), losses := [] }

theorem u9052 : Upper (D 1) (R 1) [52,72,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9052
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9053 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9053 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9053 : Upper (D 1) (R 1) [52,72,192] 13 := by
  apply FastRouting.sound _ _ [52,72,192] 13 (by decide) (choices 2) [3,17,18,48,129,130,144,257,258,272,384] r9053 c9053
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6912
  · exact u6913
  · exact u6914
  · exact u6915
  · exact u6916
  · exact u6917
  · exact u6918
  · exact u6919
  · exact u6920
  · exact u6921
  · exact u6922

def r9054 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9054 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9054 : Upper (D 1) (R 1) [52,72,257] 13 := by
  apply FastRouting.sound _ _ [52,72,257] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9054 c9054
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6923
  · exact u6924
  · exact u6925
  · exact u6926
  · exact u6927
  · exact u6928
  · exact u6929

def r9055 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9055 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9055 : Upper (D 1) (R 1) [52,72,258] 13 := by
  apply FastRouting.sound _ _ [52,72,258] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9055 c9055
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6930
  · exact u6931
  · exact u6932
  · exact u6933
  · exact u6934
  · exact u6935
  · exact u6936
  · exact u6937
  · exact u6938
  · exact u6939
  · exact u6940

def b9056 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 202, targets := 16 }], pairs := [(1,4)], upper := (rows 53 74 276 235 243 227 227 227 483), lower := (rows 53 74 276 8 16 32 64 128 256), losses := [] }

theorem u9056 : Upper (D 1) (R 1) [52,72,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9056
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9057 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9057 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9057 : Upper (D 1) (R 1) [52,72,320] 13 := by
  apply FastRouting.sound _ _ [52,72,320] 13 (by decide) (choices 2) [3,17,18,48,129,130,144] r9057 c9057
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6941
  · exact u6942
  · exact u6943
  · exact u6944
  · exact u6945
  · exact u6946
  · exact u6947

def r9058 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9058 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9058 : Upper (D 1) (R 1) [52,72,384] 13 := by
  apply FastRouting.sound _ _ [52,72,384] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9058 c9058
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6948
  · exact u6949
  · exact u6950
  · exact u6951
  · exact u6952
  · exact u6953
  · exact u6954
  · exact u6955
  · exact u6956
  · exact u6957
  · exact u6958

def b9059 : PairBound 9 := { available := 490, camps := [{ cop := 1, region := 424, targets := 16 }], pairs := [(3,4)], upper := (rows 53 82 7 490 506 490 490 490 490), lower := (rows 53 82 7 8 16 32 64 128 256), losses := [] }

theorem u9059 : Upper (D 1) (R 1) [52,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9059
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u9059
end Delivery.IrregularNine14.P01
