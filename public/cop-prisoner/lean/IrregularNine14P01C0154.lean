import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0128
import IrregularNine14P01C0129
import IrregularNine14P01C0130
import IrregularNine14P01C0131

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9240 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9240 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9240 : Upper (D 1) (R 1) [112,272,9] 13 := by
  apply FastRouting.sound _ _ [112,272,9] 13 (by decide) (choices 2) [6,34,36,96,130,132,160] r9240 c9240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7725
  · exact u7726
  · exact u7727
  · exact u7728
  · exact u7729
  · exact u7730
  · exact u7731

theorem m9241_3 : Upper (D 1) (R 1) [112,272,10,3] 13 :=
  permutation_upper _ _ _ [112,272,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7719

theorem m9241_5 : Upper (D 1) (R 1) [112,272,10,5] 13 :=
  permutation_upper _ _ _ [112,272,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7725

def r9241 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9241 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9241 : Upper (D 1) (R 1) [112,272,10] 13 := by
  apply FastRouting.sound _ _ [112,272,10] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9241 c9241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9241_3
  · exact m9241_5
  · exact u7732
  · exact u7733
  · exact u7734
  · exact u7735
  · exact u7736
  · exact u7737
  · exact u7738
  · exact u7739
  · exact u7740

def b9242 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 37 206 222 238 206 206 462), lower := (rows 113 274 37 8 16 32 64 128 256), losses := [] }

theorem u9242 : Upper (D 1) (R 1) [112,272,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9242
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9243_3 : Upper (D 1) (R 1) [112,272,34,3] 13 :=
  permutation_upper _ _ _ [112,272,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7720

theorem m9243_5 : Upper (D 1) (R 1) [112,272,34,5] 13 :=
  permutation_upper _ _ _ [112,272,9,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7726

theorem m9243_6 : Upper (D 1) (R 1) [112,272,34,6] 13 :=
  permutation_upper _ _ _ [112,272,10,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7734

theorem m9243_65 : Upper (D 1) (R 1) [112,272,34,65] 13 :=
  permutation_upper _ _ _ [112,272,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7741

def r9243 : Route 9 := (fun mask => (mask,id))

def c9243 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9243 : Upper (D 1) (R 1) [112,272,34] 13 := by
  apply FastRouting.sound _ _ [112,272,34] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9243 c9243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9243_3
  · exact m9243_5
  · exact m9243_6
  · exact m9243_65
  · exact u7746
  · exact u7747
  · exact u7748
  · exact u7749
  · exact u7750
  · exact u7751

theorem m9244_3 : Upper (D 1) (R 1) [112,272,40,3] 13 :=
  permutation_upper _ _ _ [112,272,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7721

theorem m9244_5 : Upper (D 1) (R 1) [112,272,40,5] 13 :=
  permutation_upper _ _ _ [112,272,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7727

theorem m9244_6 : Upper (D 1) (R 1) [112,272,40,6] 13 :=
  permutation_upper _ _ _ [112,272,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7735

theorem m9244_65 : Upper (D 1) (R 1) [112,272,40,65] 13 :=
  permutation_upper _ _ _ [112,272,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7742

theorem m9244_66 : Upper (D 1) (R 1) [112,272,40,66] 13 :=
  permutation_upper _ _ _ [112,272,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7747

def r9244 : Route 9 := (fun mask => (mask,id))

def c9244 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9244 : Upper (D 1) (R 1) [112,272,40] 13 := by
  apply FastRouting.sound _ _ [112,272,40] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9244 c9244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9244_3
  · exact m9244_5
  · exact m9244_6
  · exact m9244_65
  · exact m9244_66
  · exact u7752
  · exact u7753
  · exact u7754
  · exact u7755
  · exact u7756

def b9245 : PairBound 9 := { available := 143, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 100 143 159 175 207 143 399), lower := (rows 113 274 100 8 16 32 64 128 256), losses := [] }

theorem u9245 : Upper (D 1) (R 1) [112,272,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9245
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9246_6 : Upper (D 1) (R 1) [112,272,129,6] 13 :=
  permutation_upper _ _ _ [112,272,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7737

theorem m9246_34 : Upper (D 1) (R 1) [112,272,129,34] 13 :=
  permutation_upper _ _ _ [112,272,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7748

theorem m9246_36 : Upper (D 1) (R 1) [112,272,129,36] 13 :=
  permutation_upper _ _ _ [112,272,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7753

theorem m9246_96 : Upper (D 1) (R 1) [112,272,129,96] 13 :=
  permutation_upper _ _ _ [112,272,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7757

def r9246 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9246 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9246 : Upper (D 1) (R 1) [112,272,129] 13 := by
  apply FastRouting.sound _ _ [112,272,129] 13 (by decide) (choices 2) [6,34,36,96,130,132,160] r9246 c9246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9246_6
  · exact m9246_34
  · exact m9246_36
  · exact m9246_96
  · exact u7760
  · exact u7761
  · exact u7762

theorem m9247_3 : Upper (D 1) (R 1) [112,272,130,3] 13 :=
  permutation_upper _ _ _ [112,272,3,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7722

theorem m9247_5 : Upper (D 1) (R 1) [112,272,130,5] 13 :=
  permutation_upper _ _ _ [112,272,9,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7729

theorem m9247_6 : Upper (D 1) (R 1) [112,272,130,6] 13 :=
  permutation_upper _ _ _ [112,272,10,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7738

theorem m9247_33 : Upper (D 1) (R 1) [112,272,130,33] 13 :=
  permutation_upper _ _ _ [112,272,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7743

theorem m9247_34 : Upper (D 1) (R 1) [112,272,130,34] 13 :=
  permutation_upper _ _ _ [112,272,34,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7749

theorem m9247_36 : Upper (D 1) (R 1) [112,272,130,36] 13 :=
  permutation_upper _ _ _ [112,272,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7754

theorem m9247_96 : Upper (D 1) (R 1) [112,272,130,96] 13 :=
  permutation_upper _ _ _ [112,272,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7758

theorem m9247_129 : Upper (D 1) (R 1) [112,272,130,129] 13 :=
  permutation_upper _ _ _ [112,272,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7760

def r9247 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9247 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9247 : Upper (D 1) (R 1) [112,272,130] 13 := by
  apply FastRouting.sound _ _ [112,272,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9247 c9247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9247_3
  · exact m9247_5
  · exact m9247_6
  · exact m9247_33
  · exact m9247_34
  · exact m9247_36
  · exact m9247_96
  · exact m9247_129
  · exact u7763
  · exact u7764
  · exact u7765

theorem m9248_3 : Upper (D 1) (R 1) [112,272,136,3] 13 :=
  permutation_upper _ _ _ [112,272,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7723

theorem m9248_5 : Upper (D 1) (R 1) [112,272,136,5] 13 :=
  permutation_upper _ _ _ [112,272,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7730

theorem m9248_6 : Upper (D 1) (R 1) [112,272,136,6] 13 :=
  permutation_upper _ _ _ [112,272,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7739

theorem m9248_33 : Upper (D 1) (R 1) [112,272,136,33] 13 :=
  permutation_upper _ _ _ [112,272,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7744

theorem m9248_34 : Upper (D 1) (R 1) [112,272,136,34] 13 :=
  permutation_upper _ _ _ [112,272,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7750

theorem m9248_36 : Upper (D 1) (R 1) [112,272,136,36] 13 :=
  permutation_upper _ _ _ [112,272,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7755

theorem m9248_96 : Upper (D 1) (R 1) [112,272,136,96] 13 :=
  permutation_upper _ _ _ [112,272,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7759

theorem m9248_129 : Upper (D 1) (R 1) [112,272,136,129] 13 :=
  permutation_upper _ _ _ [112,272,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7761

theorem m9248_130 : Upper (D 1) (R 1) [112,272,136,130] 13 :=
  permutation_upper _ _ _ [112,272,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7764

def r9248 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9248 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9248 : Upper (D 1) (R 1) [112,272,136] 13 := by
  apply FastRouting.sound _ _ [112,272,136] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9248 c9248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9248_3
  · exact m9248_5
  · exact m9248_6
  · exact m9248_33
  · exact m9248_34
  · exact m9248_36
  · exact m9248_96
  · exact m9248_129
  · exact m9248_130
  · exact u7766
  · exact u7767

theorem m9249_3 : Upper (D 1) (R 1) [112,272,160,3] 13 :=
  permutation_upper _ _ _ [112,272,3,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7724

theorem m9249_5 : Upper (D 1) (R 1) [112,272,160,5] 13 :=
  permutation_upper _ _ _ [112,272,9,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7731

theorem m9249_6 : Upper (D 1) (R 1) [112,272,160,6] 13 :=
  permutation_upper _ _ _ [112,272,10,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7740

theorem m9249_65 : Upper (D 1) (R 1) [112,272,160,65] 13 :=
  permutation_upper _ _ _ [112,272,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7745

theorem m9249_66 : Upper (D 1) (R 1) [112,272,160,66] 13 :=
  permutation_upper _ _ _ [112,272,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7751

theorem m9249_68 : Upper (D 1) (R 1) [112,272,160,68] 13 :=
  permutation_upper _ _ _ [112,272,40,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7756

theorem m9249_129 : Upper (D 1) (R 1) [112,272,160,129] 13 :=
  permutation_upper _ _ _ [112,272,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7762

theorem m9249_130 : Upper (D 1) (R 1) [112,272,160,130] 13 :=
  permutation_upper _ _ _ [112,272,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7765

theorem m9249_132 : Upper (D 1) (R 1) [112,272,160,132] 13 :=
  permutation_upper _ _ _ [112,272,136,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7767

def r9249 : Route 9 := (fun mask => (mask,id))

def c9249 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9249 : Upper (D 1) (R 1) [112,272,160] 13 := by
  apply FastRouting.sound _ _ [112,272,160] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9249 c9249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9249_3
  · exact m9249_5
  · exact m9249_6
  · exact m9249_65
  · exact m9249_66
  · exact m9249_68
  · exact m9249_129
  · exact m9249_130
  · exact m9249_132
  · exact u7768

def r9250 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9250 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9250 : Upper (D 1) (R 1) [112,384,3] 13 := by
  apply FastRouting.sound _ _ [112,384,3] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r9250 c9250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7769
  · exact u7770
  · exact u7771
  · exact u7772
  · exact u7773
  · exact u7774
  · exact u7775

def r9251 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9251 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9251 : Upper (D 1) (R 1) [112,384,9] 13 := by
  apply FastRouting.sound _ _ [112,384,9] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r9251 c9251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7776
  · exact u7777
  · exact u7778
  · exact u7779
  · exact u7780
  · exact u7781
  · exact u7782

theorem m9252_3 : Upper (D 1) (R 1) [112,384,10,3] 13 :=
  permutation_upper _ _ _ [112,384,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7769

theorem m9252_5 : Upper (D 1) (R 1) [112,384,10,5] 13 :=
  permutation_upper _ _ _ [112,384,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7776

def r9252 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 192 => (144,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9252 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9252 : Upper (D 1) (R 1) [112,384,10] 13 := by
  apply FastRouting.sound _ _ [112,384,10] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144] r9252 c9252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9252_3
  · exact m9252_5
  · exact u7783
  · exact u7784
  · exact u7785
  · exact u7786
  · exact u7787
  · exact u7788
  · exact u7789
  · exact u7790
  · exact u7791

def b9253 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 21 238 254 238 238 238 494), lower := (rows 113 386 21 8 16 32 64 128 256), losses := [] }

theorem u9253 : Upper (D 1) (R 1) [112,384,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9253
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9254_3 : Upper (D 1) (R 1) [112,384,18,3] 13 :=
  permutation_upper _ _ _ [112,384,3,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7770

theorem m9254_5 : Upper (D 1) (R 1) [112,384,18,5] 13 :=
  permutation_upper _ _ _ [112,384,9,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7777

theorem m9254_6 : Upper (D 1) (R 1) [112,384,18,6] 13 :=
  permutation_upper _ _ _ [112,384,10,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7785

theorem m9254_33 : Upper (D 1) (R 1) [112,384,18,33] 13 :=
  permutation_upper _ _ _ [112,384,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7792

def r9254 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9254 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9254 : Upper (D 1) (R 1) [112,384,18] 13 := by
  apply FastRouting.sound _ _ [112,384,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9254 c9254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9254_3
  · exact m9254_5
  · exact m9254_6
  · exact m9254_33
  · exact u7796
  · exact u7797
  · exact u7798
  · exact u7799
  · exact u7800
  · exact u7801
  · exact u7802

theorem m9255_3 : Upper (D 1) (R 1) [112,384,24,3] 13 :=
  permutation_upper _ _ _ [112,384,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7771

theorem m9255_5 : Upper (D 1) (R 1) [112,384,24,5] 13 :=
  permutation_upper _ _ _ [112,384,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7778

theorem m9255_6 : Upper (D 1) (R 1) [112,384,24,6] 13 :=
  permutation_upper _ _ _ [112,384,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7786

theorem m9255_33 : Upper (D 1) (R 1) [112,384,24,33] 13 :=
  permutation_upper _ _ _ [112,384,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7793

theorem m9255_34 : Upper (D 1) (R 1) [112,384,24,34] 13 :=
  permutation_upper _ _ _ [112,384,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7797

def r9255 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9255 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9255 : Upper (D 1) (R 1) [112,384,24] 13 := by
  apply FastRouting.sound _ _ [112,384,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,96,129,130,132,160] r9255 c9255
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9255_3
  · exact m9255_5
  · exact m9255_6
  · exact m9255_33
  · exact m9255_34
  · exact u7803
  · exact u7804
  · exact u7805
  · exact u7806
  · exact u7807
  · exact u7808

def b9256 : PairBound 9 := { available := 207, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 113 386 52 207 223 239 207 207 463), lower := (rows 113 386 52 8 16 32 64 128 256), losses := [] }

theorem u9256 : Upper (D 1) (R 1) [112,384,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9256
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9257_6 : Upper (D 1) (R 1) [112,384,129,6] 13 :=
  permutation_upper _ _ _ [112,384,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7788

theorem m9257_18 : Upper (D 1) (R 1) [112,384,129,18] 13 :=
  permutation_upper _ _ _ [112,384,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7799

theorem m9257_20 : Upper (D 1) (R 1) [112,384,129,20] 13 :=
  permutation_upper _ _ _ [112,384,24,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7805

theorem m9257_48 : Upper (D 1) (R 1) [112,384,129,48] 13 :=
  permutation_upper _ _ _ [112,384,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7809

def r9257 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9257 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u9257 : Upper (D 1) (R 1) [112,384,129] 13 := by
  apply FastRouting.sound _ _ [112,384,129] 13 (by decide) (choices 2) [6,18,20,48] r9257 c9257
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9257_6
  · exact m9257_18
  · exact m9257_20
  · exact m9257_48

def b9258 : PairBound 9 := { available := 127, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 113 386 134 127 127 127 127 255 383), lower := (rows 113 386 134 8 16 32 64 128 256), losses := [] }

theorem u9258 : Upper (D 1) (R 1) [112,384,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9258
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9259_3 : Upper (D 1) (R 1) [112,384,136,3] 13 :=
  permutation_upper _ _ _ [112,384,3,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7774

theorem m9259_5 : Upper (D 1) (R 1) [112,384,136,5] 13 :=
  permutation_upper _ _ _ [112,384,9,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7781

theorem m9259_6 : Upper (D 1) (R 1) [112,384,136,6] 13 :=
  permutation_upper _ _ _ [112,384,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7790

theorem m9259_17 : Upper (D 1) (R 1) [112,384,136,17] 13 :=
  permutation_upper _ _ _ [112,384,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7794

theorem m9259_18 : Upper (D 1) (R 1) [112,384,136,18] 13 :=
  permutation_upper _ _ _ [112,384,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7801

theorem m9259_20 : Upper (D 1) (R 1) [112,384,136,20] 13 :=
  permutation_upper _ _ _ [112,384,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7807

theorem m9259_48 : Upper (D 1) (R 1) [112,384,136,48] 13 :=
  permutation_upper _ _ _ [112,384,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7810

def r9259 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 65 => (17,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 66 => (18,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 68 => (20,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 96 => (48,(fun i => match i.val with | 4 => 6 | 6 => 4 | _ => i)) | _ => (mask,id))

def c9259 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 144 => 7 | 272 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u9259 : Upper (D 1) (R 1) [112,384,136] 13 := by
  apply FastRouting.sound _ _ [112,384,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,48] r9259 c9259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9259_3
  · exact m9259_5
  · exact m9259_6
  · exact m9259_17
  · exact m9259_18
  · exact m9259_20
  · exact m9259_48

theorem m9260_3 : Upper (D 1) (R 1) [112,384,144,3] 13 :=
  permutation_upper _ _ _ [112,384,3,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7775

theorem m9260_5 : Upper (D 1) (R 1) [112,384,144,5] 13 :=
  permutation_upper _ _ _ [112,384,9,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7782

theorem m9260_6 : Upper (D 1) (R 1) [112,384,144,6] 13 :=
  permutation_upper _ _ _ [112,384,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7791

theorem m9260_33 : Upper (D 1) (R 1) [112,384,144,33] 13 :=
  permutation_upper _ _ _ [112,384,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7795

theorem m9260_34 : Upper (D 1) (R 1) [112,384,144,34] 13 :=
  permutation_upper _ _ _ [112,384,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7802

theorem m9260_36 : Upper (D 1) (R 1) [112,384,144,36] 13 :=
  permutation_upper _ _ _ [112,384,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7808

theorem m9260_96 : Upper (D 1) (R 1) [112,384,144,96] 13 :=
  permutation_upper _ _ _ [112,384,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 6 | 6 => 4 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 6 | 5 => 4 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7811

def r9260 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9260 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 129 => 7 | 257 => 8 | 18 => 4 | 130 => 7 | 258 => 8 | 20 => 4 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u9260 : Upper (D 1) (R 1) [112,384,144] 13 := by
  apply FastRouting.sound _ _ [112,384,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r9260 c9260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9260_3
  · exact m9260_5
  · exact m9260_6
  · exact m9260_33
  · exact m9260_34
  · exact m9260_36
  · exact m9260_96

def b9261 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 11 22 248 240 240 240 240 496), lower := (rows 263 11 22 8 16 32 64 128 256), losses := [] }

theorem u9261 : Upper (D 1) (R 1) [262,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9262 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9262 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9262 : Upper (D 1) (R 1) [262,9,48] 13 := by
  apply FastRouting.sound _ _ [262,9,48] 13 (by decide) (choices 2) [18,48,66,80,192] r9262 c9262
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7812
  · exact u7813
  · exact u7814
  · exact u7815
  · exact u7816

def b9263 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 19 14 248 240 240 240 240 496), lower := (rows 263 19 14 8 16 32 64 128 256), losses := [] }

theorem u9263 : Upper (D 1) (R 1) [262,17,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9264 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 263 19 22 232 248 232 232 232 488), lower := (rows 263 19 22 8 16 32 64 128 256), losses := [] }

theorem u9264 : Upper (D 1) (R 1) [262,17,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9265 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 19 28 234 242 226 226 226 482), lower := (rows 263 19 28 8 16 32 64 128 256), losses := [] }

theorem u9265 : Upper (D 1) (R 1) [262,17,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9266 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 19 38 248 248 248 248 248 504), lower := (rows 263 19 38 8 16 32 64 128 256), losses := [] }

theorem u9266 : Upper (D 1) (R 1) [262,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9267 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9267 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9267 : Upper (D 1) (R 1) [262,17,40] 13 := by
  apply FastRouting.sound _ _ [262,17,40] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9267 c9267
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7817
  · exact u7818
  · exact u7819
  · exact u7820
  · exact u7821
  · exact u7822
  · exact u7823

def b9268 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 19 52 234 250 234 234 234 490), lower := (rows 263 19 52 8 16 32 64 128 256), losses := [] }

theorem u9268 : Upper (D 1) (R 1) [262,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9269 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9269 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9269 : Upper (D 1) (R 1) [262,17,96] 13 := by
  apply FastRouting.sound _ _ [262,17,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9269 c9269
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7824
  · exact u7825
  · exact u7826
  · exact u7827
  · exact u7828
  · exact u7829
  · exact u7830

def b9270 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 263 26 7 248 240 240 240 240 496), lower := (rows 263 26 7 8 16 32 64 128 256), losses := [] }

theorem u9270 : Upper (D 1) (R 1) [262,24,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9271 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 26 21 234 242 226 226 226 482), lower := (rows 263 26 21 8 16 32 64 128 256), losses := [] }

theorem u9271 : Upper (D 1) (R 1) [262,24,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9272 : PairBound 9 := { available := 225, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 263 26 22 233 241 225 225 225 481), lower := (rows 263 26 22 8 16 32 64 128 256), losses := [] }

theorem u9272 : Upper (D 1) (R 1) [262,24,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9273 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9273 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9273 : Upper (D 1) (R 1) [262,24,33] 13 := by
  apply FastRouting.sound _ _ [262,24,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9273 c9273
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7831
  · exact u7832
  · exact u7833
  · exact u7834
  · exact u7835
  · exact u7836
  · exact u7837

def b9274 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 26 38 249 241 241 241 241 497), lower := (rows 263 26 38 8 16 32 64 128 256), losses := [] }

theorem u9274 : Upper (D 1) (R 1) [262,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9275 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 26 52 235 243 227 227 227 483), lower := (rows 263 26 52 8 16 32 64 128 256), losses := [] }

theorem u9275 : Upper (D 1) (R 1) [262,24,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9276 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9276 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9276 : Upper (D 1) (R 1) [262,24,96] 13 := by
  apply FastRouting.sound _ _ [262,24,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,96,129,130,144,160] r9276 c9276
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7838
  · exact u7839
  · exact u7840
  · exact u7841
  · exact u7842
  · exact u7843
  · exact u7844
  · exact u7845
  · exact u7846
  · exact u7847
  · exact u7848

def b9277 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 263 50 7 248 248 248 248 248 504), lower := (rows 263 50 7 8 16 32 64 128 256), losses := [] }

theorem u9277 : Upper (D 1) (R 1) [262,48,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9278 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9278 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9278 : Upper (D 1) (R 1) [262,48,9] 13 := by
  apply FastRouting.sound _ _ [262,48,9] 13 (by decide) (choices 2) [18,48,66,80,192] r9278 c9278
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7849
  · exact u7850
  · exact u7851
  · exact u7852
  · exact u7853

def b9279 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 50 14 249 241 241 241 241 497), lower := (rows 263 50 14 8 16 32 64 128 256), losses := [] }

theorem u9279 : Upper (D 1) (R 1) [262,48,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9279
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9280 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 21 234 250 234 234 234 490), lower := (rows 263 50 21 8 16 32 64 128 256), losses := [] }

theorem u9280 : Upper (D 1) (R 1) [262,48,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9281 : PairBound 9 := { available := 233, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 263 50 22 233 249 233 233 233 489), lower := (rows 263 50 22 8 16 32 64 128 256), losses := [] }

theorem u9281 : Upper (D 1) (R 1) [262,48,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9282 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 28 235 243 227 227 227 483), lower := (rows 263 50 28 8 16 32 64 128 256), losses := [] }

theorem u9282 : Upper (D 1) (R 1) [262,48,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9283 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 263 50 52 203 219 235 203 203 459), lower := (rows 263 50 52 8 16 32 64 128 256), losses := [] }

theorem u9283 : Upper (D 1) (R 1) [262,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9284 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9284 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9284 : Upper (D 1) (R 1) [262,48,65] 13 := by
  apply FastRouting.sound _ _ [262,48,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9284 c9284
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7854
  · exact u7855
  · exact u7856
  · exact u7857
  · exact u7858
  · exact u7859
  · exact u7860

def b9285 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 263 50 70 249 249 249 249 249 505), lower := (rows 263 50 70 8 16 32 64 128 256), losses := [] }

theorem u9285 : Upper (D 1) (R 1) [262,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9286 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9286 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9286 : Upper (D 1) (R 1) [262,48,72] 13 := by
  apply FastRouting.sound _ _ [262,48,72] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9286 c9286
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7861
  · exact u7862
  · exact u7863
  · exact u7864
  · exact u7865
  · exact u7866
  · exact u7867
  · exact u7868
  · exact u7869
  · exact u7870
  · exact u7871

def b9287 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 84 235 251 235 235 235 491), lower := (rows 263 50 84 8 16 32 64 128 256), losses := [] }

theorem u9287 : Upper (D 1) (R 1) [262,48,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9288 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9288 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9288 : Upper (D 1) (R 1) [262,48,192] 13 := by
  apply FastRouting.sound _ _ [262,48,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9288 c9288
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u7872
  · exact u7873
  · exact u7874
  · exact u7875
  · exact u7876
  · exact u7877
  · exact u7878
  · exact u7879

def b9289 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 19 22 234 242 226 226 226 482), lower := (rows 269 19 22 8 16 32 64 128 256), losses := [] }

theorem u9289 : Upper (D 1) (R 1) [268,17,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9289
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9290_18 : Upper (D 1) (R 1) [268,17,34,18] 13 :=
  permutation_upper _ _ _ [268,17,18,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7880

def r9290 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9290 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9290 : Upper (D 1) (R 1) [268,17,34] 13 := by
  apply FastRouting.sound _ _ [268,17,34] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r9290 c9290
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9290_18
  · exact u7882
  · exact u7883
  · exact u7884
  · exact u7885
  · exact u7886
  · exact u7887

def b9291 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 269 19 52 234 242 226 226 226 482), lower := (rows 269 19 52 8 16 32 64 128 256), losses := [] }

theorem u9291 : Upper (D 1) (R 1) [268,17,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9291
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9292_18 : Upper (D 1) (R 1) [268,17,96,18] 13 :=
  permutation_upper _ _ _ [268,17,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7881

theorem m9292_34 : Upper (D 1) (R 1) [268,17,96,34] 13 :=
  permutation_upper _ _ _ [268,17,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7886

theorem m9292_48 : Upper (D 1) (R 1) [268,17,96,48] 13 :=
  permutation_upper _ _ _ [268,17,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7888

theorem m9292_130 : Upper (D 1) (R 1) [268,17,96,130] 13 :=
  permutation_upper _ _ _ [268,17,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7887

theorem m9292_144 : Upper (D 1) (R 1) [268,17,96,144] 13 :=
  permutation_upper _ _ _ [268,17,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 7 | 6 => 5 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 5 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7889

def r9292 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 80 => (48,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9292 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9292 : Upper (D 1) (R 1) [268,17,96] 13 := by
  apply FastRouting.sound _ _ [268,17,96] 13 (by decide) (choices 2) [18,34,48,96,130,144,160] r9292 c9292
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9292_18
  · exact m9292_34
  · exact m9292_48
  · exact u7890
  · exact m9292_130
  · exact m9292_144
  · exact u7891

def r9293 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9293 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9293 : Upper (D 1) (R 1) [268,48,3] 13 := by
  apply FastRouting.sound _ _ [268,48,3] 13 (by decide) (choices 2) [18,48,66,80,192] r9293 c9293
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u7892
  · exact u7893
  · exact u7894
  · exact u7895
  · exact u7896

def b9294 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 269 50 21 234 242 226 226 226 482), lower := (rows 269 50 21 8 16 32 64 128 256), losses := [] }

theorem u9294 : Upper (D 1) (R 1) [268,48,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9295 : PairBound 9 := { available := 227, camps := [{ cop := 1, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 269 50 22 235 243 227 227 227 483), lower := (rows 269 50 22 8 16 32 64 128 256), losses := [] }

theorem u9295 : Upper (D 1) (R 1) [268,48,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9296 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 269 50 52 203 211 227 195 195 451), lower := (rows 269 50 52 8 16 32 64 128 256), losses := [] }

theorem u9296 : Upper (D 1) (R 1) [268,48,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9296
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9297_18 : Upper (D 1) (R 1) [268,48,65,18] 13 :=
  permutation_upper _ _ _ [268,48,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7900

theorem m9297_48 : Upper (D 1) (R 1) [268,48,65,48] 13 :=
  permutation_upper _ _ _ [268,48,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7904

def r9297 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9297 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9297 : Upper (D 1) (R 1) [268,48,65] 13 := by
  apply FastRouting.sound _ _ [268,48,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9297 c9297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9297_18
  · exact m9297_48
  · exact u7907
  · exact u7908
  · exact u7909
  · exact u7910
  · exact u7911

theorem m9298_3 : Upper (D 1) (R 1) [268,48,66,3] 13 :=
  permutation_upper _ _ _ [268,48,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7894

theorem m9298_17 : Upper (D 1) (R 1) [268,48,66,17] 13 :=
  permutation_upper _ _ _ [268,48,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7897

theorem m9298_18 : Upper (D 1) (R 1) [268,48,66,18] 13 :=
  permutation_upper _ _ _ [268,48,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7901

theorem m9298_48 : Upper (D 1) (R 1) [268,48,66,48] 13 :=
  permutation_upper _ _ _ [268,48,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7905

theorem m9298_65 : Upper (D 1) (R 1) [268,48,66,65] 13 :=
  permutation_upper _ _ _ [268,48,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7907

theorem m9298_129 : Upper (D 1) (R 1) [268,48,66,129] 13 :=
  permutation_upper _ _ _ [268,48,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7909

def r9298 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9298 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9298 : Upper (D 1) (R 1) [268,48,66] 13 := by
  apply FastRouting.sound _ _ [268,48,66] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9298 c9298
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9298_3
  · exact m9298_17
  · exact m9298_18
  · exact m9298_48
  · exact m9298_65
  · exact u7912
  · exact u7913
  · exact m9298_129
  · exact u7914
  · exact u7915
  · exact u7916

theorem m9299_3 : Upper (D 1) (R 1) [268,48,80,3] 13 :=
  permutation_upper _ _ _ [268,48,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7895

theorem m9299_33 : Upper (D 1) (R 1) [268,48,80,33] 13 :=
  permutation_upper _ _ _ [268,48,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7898

theorem m9299_34 : Upper (D 1) (R 1) [268,48,80,34] 13 :=
  permutation_upper _ _ _ [268,48,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7902

theorem m9299_65 : Upper (D 1) (R 1) [268,48,80,65] 13 :=
  permutation_upper _ _ _ [268,48,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7908

theorem m9299_66 : Upper (D 1) (R 1) [268,48,80,66] 13 :=
  permutation_upper _ _ _ [268,48,66,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7913

theorem m9299_129 : Upper (D 1) (R 1) [268,48,80,129] 13 :=
  permutation_upper _ _ _ [268,48,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7910

theorem m9299_130 : Upper (D 1) (R 1) [268,48,80,130] 13 :=
  permutation_upper _ _ _ [268,48,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7915

def r9299 : Route 9 := (fun mask => (mask,id))

def c9299 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9299 : Upper (D 1) (R 1) [268,48,80] 13 := by
  apply FastRouting.sound _ _ [268,48,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9299 c9299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9299_3
  · exact m9299_33
  · exact m9299_34
  · exact m9299_65
  · exact m9299_66
  · exact u7917
  · exact m9299_129
  · exact m9299_130
  · exact u7918
  · exact u7919

#print axioms u9299
end Delivery.IrregularNine14.P01
