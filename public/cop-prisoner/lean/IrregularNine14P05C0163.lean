import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0144
import IrregularNine14P05C0145
import IrregularNine14P05C0146
import IrregularNine14P05C0147
import IrregularNine14P05C0148
import IrregularNine14P05C0149
import IrregularNine14P05C0150
import IrregularNine14P05C0151
import IrregularNine14P05C0152
import IrregularNine14P05C0153
import IrregularNine14P05C0154
import IrregularNine14P05C0155
import IrregularNine14P05C0156
import IrregularNine14P05C0157
import IrregularNine14P05C0158

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9780_3 : Upper (D 5) (R 5) [18,96,33,3] 13 :=
  permutation_upper _ _ _ [6,20,96,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8757

theorem m9780_5 : Upper (D 5) (R 5) [18,96,33,5] 13 :=
  permutation_upper _ _ _ [6,24,34,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8778

theorem m9780_6 : Upper (D 5) (R 5) [18,96,33,6] 13 :=
  permutation_upper _ _ _ [6,40,96,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9008

def r9780 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9780 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9780 : Upper (D 5) (R 5) [18,96,33] 13 := by
  apply FastRouting.sound _ _ [18,96,33] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9780 c9780
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9780_3
  · exact m9780_5
  · exact m9780_6
  · exact u9350
  · exact u9351
  · exact u9352
  · exact u9353

def b9781 : PairBound 9 := { available := 397, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 19 98 38 397 413 429 461 397 397), lower := (rows 19 98 38 8 16 32 64 128 256), losses := [] }

theorem u9781 : Upper (D 5) (R 5) [18,96,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9781
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9782_3 : Upper (D 5) (R 5) [18,96,40,3] 13 :=
  permutation_upper _ _ _ [6,20,96,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8756

theorem m9782_5 : Upper (D 5) (R 5) [18,96,40,5] 13 :=
  permutation_upper _ _ _ [6,24,33,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8773

theorem m9782_6 : Upper (D 5) (R 5) [18,96,40,6] 13 :=
  permutation_upper _ _ _ [6,33,96,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8889

def r9782 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9782 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9782 : Upper (D 5) (R 5) [18,96,40] 13 := by
  apply FastRouting.sound _ _ [18,96,40] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9782 c9782
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9782_3
  · exact m9782_5
  · exact m9782_6
  · exact u9357
  · exact u9358
  · exact u9359
  · exact u9360

theorem m9783_3 : Upper (D 5) (R 5) [18,96,129,3] 13 :=
  permutation_upper _ _ _ [6,20,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8759

theorem m9783_5 : Upper (D 5) (R 5) [18,96,129,5] 13 :=
  permutation_upper _ _ _ [6,24,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8800

theorem m9783_6 : Upper (D 5) (R 5) [18,96,129,6] 13 :=
  permutation_upper _ _ _ [6,72,160,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9171

theorem m9783_33 : Upper (D 5) (R 5) [18,96,129,33] 13 :=
  permutation_upper _ _ _ [18,96,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9350

theorem m9783_34 : Upper (D 5) (R 5) [18,96,129,34] 13 :=
  permutation_upper _ _ _ [18,96,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9354

theorem m9783_36 : Upper (D 5) (R 5) [18,96,129,36] 13 :=
  permutation_upper _ _ _ [18,96,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9357

def r9783 : Route 9 := (fun mask => (mask,id))

def c9783 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9783 : Upper (D 5) (R 5) [18,96,129] 13 := by
  apply FastRouting.sound _ _ [18,96,129] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9783 c9783
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9783_3
  · exact m9783_5
  · exact m9783_6
  · exact m9783_33
  · exact m9783_34
  · exact m9783_36
  · exact u9361
  · exact u9362
  · exact u9363
  · exact u9364

theorem m9784_5 : Upper (D 5) (R 5) [18,96,130,5] 13 :=
  permutation_upper _ _ _ [6,24,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8808

theorem m9784_33 : Upper (D 5) (R 5) [18,96,130,33] 13 :=
  permutation_upper _ _ _ [18,96,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9351

theorem m9784_36 : Upper (D 5) (R 5) [18,96,130,36] 13 :=
  permutation_upper _ _ _ [18,96,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9358

theorem m9784_257 : Upper (D 5) (R 5) [18,96,130,257] 13 :=
  permutation_upper _ _ _ [18,96,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9362

def r9784 : Route 9 := (fun mask => (mask,id))

def c9784 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9784 : Upper (D 5) (R 5) [18,96,130] 13 := by
  apply FastRouting.sound _ _ [18,96,130] 13 (by decide) (choices 2) [5,33,36,257,260,288] r9784 c9784
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9784_5
  · exact m9784_33
  · exact m9784_36
  · exact m9784_257
  · exact u9365
  · exact u9366

theorem m9785_3 : Upper (D 5) (R 5) [18,96,136,3] 13 :=
  permutation_upper _ _ _ [6,20,96,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8758

theorem m9785_5 : Upper (D 5) (R 5) [18,96,136,5] 13 :=
  permutation_upper _ _ _ [6,24,65,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8794

theorem m9785_6 : Upper (D 5) (R 5) [18,96,136,6] 13 :=
  permutation_upper _ _ _ [6,65,160,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9101

theorem m9785_33 : Upper (D 5) (R 5) [18,96,136,33] 13 :=
  permutation_upper _ _ _ [18,96,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9352

theorem m9785_34 : Upper (D 5) (R 5) [18,96,136,34] 13 :=
  permutation_upper _ _ _ [18,96,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9355

theorem m9785_36 : Upper (D 5) (R 5) [18,96,136,36] 13 :=
  permutation_upper _ _ _ [18,96,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9359

theorem m9785_257 : Upper (D 5) (R 5) [18,96,136,257] 13 :=
  permutation_upper _ _ _ [18,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9363

theorem m9785_258 : Upper (D 5) (R 5) [18,96,136,258] 13 :=
  permutation_upper _ _ _ [18,96,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9365

def r9785 : Route 9 := (fun mask => (mask,id))

def c9785 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9785 : Upper (D 5) (R 5) [18,96,136] 13 := by
  apply FastRouting.sound _ _ [18,96,136] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9785 c9785
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9785_3
  · exact m9785_5
  · exact m9785_6
  · exact m9785_33
  · exact m9785_34
  · exact m9785_36
  · exact m9785_257
  · exact m9785_258
  · exact u9367
  · exact u9368

theorem m9786_3 : Upper (D 5) (R 5) [18,96,160,3] 13 :=
  permutation_upper _ _ _ [6,20,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8760

theorem m9786_5 : Upper (D 5) (R 5) [18,96,160,5] 13 :=
  permutation_upper _ _ _ [6,24,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8816

theorem m9786_6 : Upper (D 5) (R 5) [18,96,160,6] 13 :=
  permutation_upper _ _ _ [6,96,160,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9201

theorem m9786_257 : Upper (D 5) (R 5) [18,96,160,257] 13 :=
  permutation_upper _ _ _ [18,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9364

theorem m9786_258 : Upper (D 5) (R 5) [18,96,160,258] 13 :=
  permutation_upper _ _ _ [18,96,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9366

theorem m9786_260 : Upper (D 5) (R 5) [18,96,160,260] 13 :=
  permutation_upper _ _ _ [18,96,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9368

def r9786 : Route 9 := (fun mask => (mask,id))

def c9786 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 129 => 7 | 18 => 4 | 34 => 5 | 66 => 6 | 130 => 7 | 20 => 4 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9786 : Upper (D 5) (R 5) [18,96,160] 13 := by
  apply FastRouting.sound _ _ [18,96,160] 13 (by decide) (choices 2) [3,5,6,257,258,260] r9786 c9786
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9786_3
  · exact m9786_5
  · exact m9786_6
  · exact m9786_257
  · exact m9786_258
  · exact m9786_260

theorem m9787_3 : Upper (D 5) (R 5) [18,96,384,3] 13 :=
  permutation_upper _ _ _ [6,20,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8761

theorem m9787_5 : Upper (D 5) (R 5) [18,96,384,5] 13 :=
  permutation_upper _ _ _ [6,24,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8824

theorem m9787_6 : Upper (D 5) (R 5) [18,96,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,18] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9207

theorem m9787_33 : Upper (D 5) (R 5) [18,96,384,33] 13 :=
  permutation_upper _ _ _ [18,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9353

theorem m9787_34 : Upper (D 5) (R 5) [18,96,384,34] 13 :=
  permutation_upper _ _ _ [18,96,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9356

theorem m9787_36 : Upper (D 5) (R 5) [18,96,384,36] 13 :=
  permutation_upper _ _ _ [18,96,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9360

def r9787 : Route 9 := (fun mask => (mask,id))

def c9787 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9787 : Upper (D 5) (R 5) [18,96,384] 13 := by
  apply FastRouting.sound _ _ [18,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9787 c9787
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9787_3
  · exact m9787_5
  · exact m9787_6
  · exact m9787_33
  · exact m9787_34
  · exact m9787_36

theorem m9788_3 : Upper (D 5) (R 5) [18,192,33,3] 13 :=
  permutation_upper _ _ _ [6,20,192,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8763

theorem m9788_5 : Upper (D 5) (R 5) [18,192,33,5] 13 :=
  permutation_upper _ _ _ [6,24,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8779

theorem m9788_6 : Upper (D 5) (R 5) [18,192,33,6] 13 :=
  permutation_upper _ _ _ [6,40,192,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9016

def r9788 : Route 9 := (fun mask => (mask,id))

def c9788 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9788 : Upper (D 5) (R 5) [18,192,33] 13 := by
  apply FastRouting.sound _ _ [18,192,33] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9788 c9788
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9788_3
  · exact m9788_5
  · exact m9788_6
  · exact u9369
  · exact u9370
  · exact u9371
  · exact u9372
  · exact u9373
  · exact u9374
  · exact u9375

theorem m9789_5 : Upper (D 5) (R 5) [18,192,34,5] 13 :=
  permutation_upper _ _ _ [6,24,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8787

theorem m9789_33 : Upper (D 5) (R 5) [18,192,34,33] 13 :=
  permutation_upper _ _ _ [18,192,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9370

def r9789 : Route 9 := (fun mask => (mask,id))

def c9789 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9789 : Upper (D 5) (R 5) [18,192,34] 13 := by
  apply FastRouting.sound _ _ [18,192,34] 13 (by decide) (choices 2) [5,33,36,257,260,288] r9789 c9789
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9789_5
  · exact m9789_33
  · exact u9376
  · exact u9377
  · exact u9378
  · exact u9379

theorem m9790_3 : Upper (D 5) (R 5) [18,192,40,3] 13 :=
  permutation_upper _ _ _ [6,20,192,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8762

theorem m9790_5 : Upper (D 5) (R 5) [18,192,40,5] 13 :=
  permutation_upper _ _ _ [6,24,33,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8774

theorem m9790_6 : Upper (D 5) (R 5) [18,192,40,6] 13 :=
  permutation_upper _ _ _ [6,33,192,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8898

theorem m9790_33 : Upper (D 5) (R 5) [18,192,40,33] 13 :=
  permutation_upper _ _ _ [18,192,33,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9371

theorem m9790_34 : Upper (D 5) (R 5) [18,192,40,34] 13 :=
  permutation_upper _ _ _ [18,192,34,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9376

def r9790 : Route 9 := (fun mask => (mask,id))

def c9790 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9790 : Upper (D 5) (R 5) [18,192,40] 13 := by
  apply FastRouting.sound _ _ [18,192,40] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9790 c9790
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9790_3
  · exact m9790_5
  · exact m9790_6
  · exact m9790_33
  · exact m9790_34
  · exact u9380
  · exact u9381
  · exact u9382
  · exact u9383
  · exact u9384

theorem m9791_3 : Upper (D 5) (R 5) [18,192,257,3] 13 :=
  permutation_upper _ _ _ [6,20,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8765

theorem m9791_5 : Upper (D 5) (R 5) [18,192,257,5] 13 :=
  permutation_upper _ _ _ [6,24,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8801

theorem m9791_6 : Upper (D 5) (R 5) [18,192,257,6] 13 :=
  permutation_upper _ _ _ [6,72,384,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9183

theorem m9791_33 : Upper (D 5) (R 5) [18,192,257,33] 13 :=
  permutation_upper _ _ _ [18,192,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9372

theorem m9791_34 : Upper (D 5) (R 5) [18,192,257,34] 13 :=
  permutation_upper _ _ _ [18,192,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9377

theorem m9791_36 : Upper (D 5) (R 5) [18,192,257,36] 13 :=
  permutation_upper _ _ _ [18,192,40,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9381

def r9791 : Route 9 := (fun mask => (mask,id))

def c9791 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9791 : Upper (D 5) (R 5) [18,192,257] 13 := by
  apply FastRouting.sound _ _ [18,192,257] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9791 c9791
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9791_3
  · exact m9791_5
  · exact m9791_6
  · exact m9791_33
  · exact m9791_34
  · exact m9791_36

theorem m9792_5 : Upper (D 5) (R 5) [18,192,258,5] 13 :=
  permutation_upper _ _ _ [6,24,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8809

theorem m9792_33 : Upper (D 5) (R 5) [18,192,258,33] 13 :=
  permutation_upper _ _ _ [18,192,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9373

theorem m9792_36 : Upper (D 5) (R 5) [18,192,258,36] 13 :=
  permutation_upper _ _ _ [18,192,40,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9382

def r9792 : Route 9 := (fun mask => (mask,id))

def c9792 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9792 : Upper (D 5) (R 5) [18,192,258] 13 := by
  apply FastRouting.sound _ _ [18,192,258] 13 (by decide) (choices 2) [5,33,36] r9792 c9792
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m9792_5
  · exact m9792_33
  · exact m9792_36

theorem m9793_3 : Upper (D 5) (R 5) [18,192,264,3] 13 :=
  permutation_upper _ _ _ [6,20,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8764

theorem m9793_5 : Upper (D 5) (R 5) [18,192,264,5] 13 :=
  permutation_upper _ _ _ [6,24,65,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8795

theorem m9793_6 : Upper (D 5) (R 5) [18,192,264,6] 13 :=
  permutation_upper _ _ _ [6,65,384,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9114

theorem m9793_33 : Upper (D 5) (R 5) [18,192,264,33] 13 :=
  permutation_upper _ _ _ [18,192,33,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9374

theorem m9793_34 : Upper (D 5) (R 5) [18,192,264,34] 13 :=
  permutation_upper _ _ _ [18,192,34,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9378

theorem m9793_36 : Upper (D 5) (R 5) [18,192,264,36] 13 :=
  permutation_upper _ _ _ [18,192,40,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9383

def r9793 : Route 9 := (fun mask => (mask,id))

def c9793 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9793 : Upper (D 5) (R 5) [18,192,264] 13 := by
  apply FastRouting.sound _ _ [18,192,264] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9793 c9793
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9793_3
  · exact m9793_5
  · exact m9793_6
  · exact m9793_33
  · exact m9793_34
  · exact m9793_36

theorem m9794_3 : Upper (D 5) (R 5) [18,192,288,3] 13 :=
  permutation_upper _ _ _ [6,20,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8766

theorem m9794_5 : Upper (D 5) (R 5) [18,192,288,5] 13 :=
  permutation_upper _ _ _ [6,24,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8817

theorem m9794_6 : Upper (D 5) (R 5) [18,192,288,6] 13 :=
  permutation_upper _ _ _ [6,96,384,20] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9208

theorem m9794_33 : Upper (D 5) (R 5) [18,192,288,33] 13 :=
  permutation_upper _ _ _ [18,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9375

theorem m9794_34 : Upper (D 5) (R 5) [18,192,288,34] 13 :=
  permutation_upper _ _ _ [18,192,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9379

theorem m9794_36 : Upper (D 5) (R 5) [18,192,288,36] 13 :=
  permutation_upper _ _ _ [18,192,40,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9384

def r9794 : Route 9 := (fun mask => (mask,id))

def c9794 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9794 : Upper (D 5) (R 5) [18,192,288] 13 := by
  apply FastRouting.sound _ _ [18,192,288] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9794 c9794
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9794_3
  · exact m9794_5
  · exact m9794_6
  · exact m9794_33
  · exact m9794_34
  · exact m9794_36

theorem m9795_3 : Upper (D 5) (R 5) [24,33,66,3] 13 :=
  permutation_upper _ _ _ [6,17,34,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8677

theorem m9795_5 : Upper (D 5) (R 5) [24,33,66,5] 13 :=
  permutation_upper _ _ _ [6,17,72,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8704

theorem m9795_6 : Upper (D 5) (R 5) [24,33,66,6] 13 :=
  permutation_upper _ _ _ [6,40,66,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8979

theorem m9795_33 : Upper (D 5) (R 5) [24,33,66,33] 13 :=
  permutation_upper _ _ _ [18,33,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9214

theorem m9795_34 : Upper (D 5) (R 5) [24,33,66,34] 13 :=
  permutation_upper _ _ _ [18,36,33,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9235

theorem m9795_36 : Upper (D 5) (R 5) [24,33,66,36] 13 :=
  permutation_upper _ _ _ [18,36,72,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9256

theorem m9795_129 : Upper (D 5) (R 5) [24,33,66,129] 13 :=
  permutation_upper _ _ _ [18,65,33,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9277

theorem m9795_130 : Upper (D 5) (R 5) [24,33,66,130] 13 :=
  permutation_upper _ _ _ [18,68,33,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9304

theorem m9795_132 : Upper (D 5) (R 5) [24,33,66,132] 13 :=
  permutation_upper _ _ _ [18,68,136,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9333

theorem m9795_160 : Upper (D 5) (R 5) [24,33,66,160] 13 :=
  permutation_upper _ _ _ [18,96,33,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9352

theorem m9795_384 : Upper (D 5) (R 5) [24,33,66,384] 13 :=
  permutation_upper _ _ _ [18,192,33,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9374

def r9795 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9795 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9795 : Upper (D 5) (R 5) [24,33,66] 13 := by
  apply FastRouting.sound _ _ [24,33,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9795 c9795
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9795_3
  · exact m9795_5
  · exact m9795_6
  · exact m9795_33
  · exact m9795_34
  · exact m9795_36
  · exact m9795_129
  · exact m9795_130
  · exact m9795_132
  · exact m9795_160
  · exact m9795_384

theorem m9796_3 : Upper (D 5) (R 5) [24,33,96,3] 13 :=
  permutation_upper _ _ _ [6,17,34,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8678

theorem m9796_5 : Upper (D 5) (R 5) [24,33,96,5] 13 :=
  permutation_upper _ _ _ [6,17,96,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8713

theorem m9796_6 : Upper (D 5) (R 5) [24,33,96,6] 13 :=
  permutation_upper _ _ _ [6,40,96,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9006

theorem m9796_129 : Upper (D 5) (R 5) [24,33,96,129] 13 :=
  permutation_upper _ _ _ [18,65,33,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9278

theorem m9796_130 : Upper (D 5) (R 5) [24,33,96,130] 13 :=
  permutation_upper _ _ _ [18,68,33,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9305

theorem m9796_132 : Upper (D 5) (R 5) [24,33,96,132] 13 :=
  permutation_upper _ _ _ [18,68,160,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9340

theorem m9796_384 : Upper (D 5) (R 5) [24,33,96,384] 13 :=
  permutation_upper _ _ _ [18,192,33,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9375

def r9796 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9796 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9796 : Upper (D 5) (R 5) [24,33,96] 13 := by
  apply FastRouting.sound _ _ [24,33,96] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9796 c9796
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9796_3
  · exact m9796_5
  · exact m9796_6
  · exact m9796_129
  · exact m9796_130
  · exact m9796_132
  · exact m9796_384

theorem m9797_3 : Upper (D 5) (R 5) [24,33,192,3] 13 :=
  permutation_upper _ _ _ [6,17,34,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8679

theorem m9797_5 : Upper (D 5) (R 5) [24,33,192,5] 13 :=
  permutation_upper _ _ _ [6,17,192,34] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8722

theorem m9797_6 : Upper (D 5) (R 5) [24,33,192,6] 13 :=
  permutation_upper _ _ _ [6,40,192,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9014

theorem m9797_33 : Upper (D 5) (R 5) [24,33,192,33] 13 :=
  permutation_upper _ _ _ [18,33,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9215

theorem m9797_34 : Upper (D 5) (R 5) [24,33,192,34] 13 :=
  permutation_upper _ _ _ [18,36,33,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9236

theorem m9797_36 : Upper (D 5) (R 5) [24,33,192,36] 13 :=
  permutation_upper _ _ _ [18,36,192,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9267

theorem m9797_257 : Upper (D 5) (R 5) [24,33,192,257] 13 :=
  permutation_upper _ _ _ [18,65,33,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9279

theorem m9797_258 : Upper (D 5) (R 5) [24,33,192,258] 13 :=
  permutation_upper _ _ _ [18,68,33,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9306

theorem m9797_260 : Upper (D 5) (R 5) [24,33,192,260] 13 :=
  permutation_upper _ _ _ [18,68,384,33] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9347

theorem m9797_288 : Upper (D 5) (R 5) [24,33,192,288] 13 :=
  permutation_upper _ _ _ [18,96,33,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9353

def r9797 : Route 9 := (fun mask => (mask,id))

def c9797 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9797 : Upper (D 5) (R 5) [24,33,192] 13 := by
  apply FastRouting.sound _ _ [24,33,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9797 c9797
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9797_3
  · exact m9797_5
  · exact m9797_6
  · exact m9797_33
  · exact m9797_34
  · exact m9797_36
  · exact m9797_257
  · exact m9797_258
  · exact m9797_260
  · exact m9797_288

theorem m9798_3 : Upper (D 5) (R 5) [24,36,65,3] 13 :=
  permutation_upper _ _ _ [6,17,40,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8685

theorem m9798_5 : Upper (D 5) (R 5) [24,36,65,5] 13 :=
  permutation_upper _ _ _ [6,17,66,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8697

theorem m9798_6 : Upper (D 5) (R 5) [24,36,65,6] 13 :=
  permutation_upper _ _ _ [6,36,72,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8930

theorem m9798_33 : Upper (D 5) (R 5) [24,36,65,33] 13 :=
  permutation_upper _ _ _ [18,33,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9219

theorem m9798_34 : Upper (D 5) (R 5) [24,36,65,34] 13 :=
  permutation_upper _ _ _ [18,36,40,65] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9239

theorem m9798_36 : Upper (D 5) (R 5) [24,36,65,36] 13 :=
  permutation_upper _ _ _ [18,36,65,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9244

theorem m9798_129 : Upper (D 5) (R 5) [24,36,65,129] 13 :=
  permutation_upper _ _ _ [18,65,40,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9286

theorem m9798_130 : Upper (D 5) (R 5) [24,36,65,130] 13 :=
  permutation_upper _ _ _ [18,68,40,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9316

theorem m9798_132 : Upper (D 5) (R 5) [24,36,65,132] 13 :=
  permutation_upper _ _ _ [18,68,129,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9323

theorem m9798_160 : Upper (D 5) (R 5) [24,36,65,160] 13 :=
  permutation_upper _ _ _ [18,96,40,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9357

theorem m9798_384 : Upper (D 5) (R 5) [24,36,65,384] 13 :=
  permutation_upper _ _ _ [18,192,40,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9381

def r9798 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9798 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9798 : Upper (D 5) (R 5) [24,36,65] 13 := by
  apply FastRouting.sound _ _ [24,36,65] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9798 c9798
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9798_3
  · exact m9798_5
  · exact m9798_6
  · exact m9798_33
  · exact m9798_34
  · exact m9798_36
  · exact m9798_129
  · exact m9798_130
  · exact m9798_132
  · exact m9798_160
  · exact m9798_384

theorem m9799_3 : Upper (D 5) (R 5) [24,36,66,3] 13 :=
  permutation_upper _ _ _ [6,17,40,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8686

theorem m9799_5 : Upper (D 5) (R 5) [24,36,66,5] 13 :=
  permutation_upper _ _ _ [6,17,72,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8705

theorem m9799_6 : Upper (D 5) (R 5) [24,36,66,6] 13 :=
  permutation_upper _ _ _ [6,36,66,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8923

theorem m9799_33 : Upper (D 5) (R 5) [24,36,66,33] 13 :=
  permutation_upper _ _ _ [18,33,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9221

theorem m9799_34 : Upper (D 5) (R 5) [24,36,66,34] 13 :=
  permutation_upper _ _ _ [18,36,40,68] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9240

theorem m9799_36 : Upper (D 5) (R 5) [24,36,66,36] 13 :=
  permutation_upper _ _ _ [18,36,72,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9258

theorem m9799_129 : Upper (D 5) (R 5) [24,36,66,129] 13 :=
  permutation_upper _ _ _ [18,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9288

theorem m9799_130 : Upper (D 5) (R 5) [24,36,66,130] 13 :=
  permutation_upper _ _ _ [18,68,40,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9318

theorem m9799_132 : Upper (D 5) (R 5) [24,36,66,132] 13 :=
  permutation_upper _ _ _ [18,68,136,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9335

theorem m9799_160 : Upper (D 5) (R 5) [24,36,66,160] 13 :=
  permutation_upper _ _ _ [18,96,40,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9359

theorem m9799_384 : Upper (D 5) (R 5) [24,36,66,384] 13 :=
  permutation_upper _ _ _ [18,192,40,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9383

def r9799 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9799 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9799 : Upper (D 5) (R 5) [24,36,66] 13 := by
  apply FastRouting.sound _ _ [24,36,66] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,384] r9799 c9799
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9799_3
  · exact m9799_5
  · exact m9799_6
  · exact m9799_33
  · exact m9799_34
  · exact m9799_36
  · exact m9799_129
  · exact m9799_130
  · exact m9799_132
  · exact m9799_160
  · exact m9799_384

theorem m9800_3 : Upper (D 5) (R 5) [24,36,192,3] 13 :=
  permutation_upper _ _ _ [6,17,40,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8688

theorem m9800_5 : Upper (D 5) (R 5) [24,36,192,5] 13 :=
  permutation_upper _ _ _ [6,17,192,36] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8723

theorem m9800_6 : Upper (D 5) (R 5) [24,36,192,6] 13 :=
  permutation_upper _ _ _ [6,36,192,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8948

theorem m9800_33 : Upper (D 5) (R 5) [24,36,192,33] 13 :=
  permutation_upper _ _ _ [18,33,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9222

theorem m9800_34 : Upper (D 5) (R 5) [24,36,192,34] 13 :=
  permutation_upper _ _ _ [18,36,40,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9241

theorem m9800_36 : Upper (D 5) (R 5) [24,36,192,36] 13 :=
  permutation_upper _ _ _ [18,36,192,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9269

theorem m9800_257 : Upper (D 5) (R 5) [24,36,192,257] 13 :=
  permutation_upper _ _ _ [18,65,40,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9290

theorem m9800_258 : Upper (D 5) (R 5) [24,36,192,258] 13 :=
  permutation_upper _ _ _ [18,68,40,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9320

theorem m9800_260 : Upper (D 5) (R 5) [24,36,192,260] 13 :=
  permutation_upper _ _ _ [18,68,384,36] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9349

theorem m9800_288 : Upper (D 5) (R 5) [24,36,192,288] 13 :=
  permutation_upper _ _ _ [18,96,40,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9360

def r9800 : Route 9 := (fun mask => (mask,id))

def c9800 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9800 : Upper (D 5) (R 5) [24,36,192] 13 := by
  apply FastRouting.sound _ _ [24,36,192] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9800 c9800
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9800_3
  · exact m9800_5
  · exact m9800_6
  · exact m9800_33
  · exact m9800_34
  · exact m9800_36
  · exact m9800_257
  · exact m9800_258
  · exact m9800_260
  · exact m9800_288

theorem m9801_3 : Upper (D 5) (R 5) [24,65,130,3] 13 :=
  permutation_upper _ _ _ [6,17,66,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8699

theorem m9801_5 : Upper (D 5) (R 5) [24,65,130,5] 13 :=
  permutation_upper _ _ _ [6,17,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8707

theorem m9801_6 : Upper (D 5) (R 5) [24,65,130,6] 13 :=
  permutation_upper _ _ _ [6,68,136,17] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9125

theorem m9801_33 : Upper (D 5) (R 5) [24,65,130,33] 13 :=
  permutation_upper _ _ _ [18,33,65,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9224

theorem m9801_34 : Upper (D 5) (R 5) [24,65,130,34] 13 :=
  permutation_upper _ _ _ [18,36,65,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9247

theorem m9801_36 : Upper (D 5) (R 5) [24,65,130,36] 13 :=
  permutation_upper _ _ _ [18,36,72,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9259

theorem m9801_257 : Upper (D 5) (R 5) [24,65,130,257] 13 :=
  permutation_upper _ _ _ [18,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9292

theorem m9801_258 : Upper (D 5) (R 5) [24,65,130,258] 13 :=
  permutation_upper _ _ _ [18,68,129,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9326

theorem m9801_260 : Upper (D 5) (R 5) [24,65,130,260] 13 :=
  permutation_upper _ _ _ [18,68,136,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9336

theorem m9801_288 : Upper (D 5) (R 5) [24,65,130,288] 13 :=
  permutation_upper _ _ _ [18,96,129,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9363

def r9801 : Route 9 := (fun mask => (mask,id))

def c9801 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9801 : Upper (D 5) (R 5) [24,65,130] 13 := by
  apply FastRouting.sound _ _ [24,65,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9801 c9801
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9801_3
  · exact m9801_5
  · exact m9801_6
  · exact m9801_33
  · exact m9801_34
  · exact m9801_36
  · exact m9801_257
  · exact m9801_258
  · exact m9801_260
  · exact m9801_288

theorem m9802_3 : Upper (D 5) (R 5) [24,65,160,3] 13 :=
  permutation_upper _ _ _ [6,17,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8700

theorem m9802_5 : Upper (D 5) (R 5) [24,65,160,5] 13 :=
  permutation_upper _ _ _ [6,17,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8716

theorem m9802_6 : Upper (D 5) (R 5) [24,65,160,6] 13 :=
  permutation_upper _ _ _ [6,72,160,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9169

theorem m9802_33 : Upper (D 5) (R 5) [24,65,160,33] 13 :=
  permutation_upper _ _ _ [18,33,65,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9225

theorem m9802_34 : Upper (D 5) (R 5) [24,65,160,34] 13 :=
  permutation_upper _ _ _ [18,36,65,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9248

theorem m9802_36 : Upper (D 5) (R 5) [24,65,160,36] 13 :=
  permutation_upper _ _ _ [18,36,96,129] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9264

theorem m9802_257 : Upper (D 5) (R 5) [24,65,160,257] 13 :=
  permutation_upper _ _ _ [18,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9293

theorem m9802_258 : Upper (D 5) (R 5) [24,65,160,258] 13 :=
  permutation_upper _ _ _ [18,68,129,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9327

theorem m9802_260 : Upper (D 5) (R 5) [24,65,160,260] 13 :=
  permutation_upper _ _ _ [18,68,160,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9343

theorem m9802_288 : Upper (D 5) (R 5) [24,65,160,288] 13 :=
  permutation_upper _ _ _ [18,96,129,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9364

def r9802 : Route 9 := (fun mask => (mask,id))

def c9802 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9802 : Upper (D 5) (R 5) [24,65,160] 13 := by
  apply FastRouting.sound _ _ [24,65,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9802 c9802
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9802_3
  · exact m9802_5
  · exact m9802_6
  · exact m9802_33
  · exact m9802_34
  · exact m9802_36
  · exact m9802_257
  · exact m9802_258
  · exact m9802_260
  · exact m9802_288

theorem m9803_3 : Upper (D 5) (R 5) [24,65,384,3] 13 :=
  permutation_upper _ _ _ [6,17,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8701

theorem m9803_5 : Upper (D 5) (R 5) [24,65,384,5] 13 :=
  permutation_upper _ _ _ [6,17,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8725

theorem m9803_6 : Upper (D 5) (R 5) [24,65,384,6] 13 :=
  permutation_upper _ _ _ [6,72,384,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9181

theorem m9803_33 : Upper (D 5) (R 5) [24,65,384,33] 13 :=
  permutation_upper _ _ _ [18,33,65,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9226

theorem m9803_34 : Upper (D 5) (R 5) [24,65,384,34] 13 :=
  permutation_upper _ _ _ [18,36,65,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9249

theorem m9803_36 : Upper (D 5) (R 5) [24,65,384,36] 13 :=
  permutation_upper _ _ _ [18,36,192,257] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9270

def r9803 : Route 9 := (fun mask => (mask,id))

def c9803 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9803 : Upper (D 5) (R 5) [24,65,384] 13 := by
  apply FastRouting.sound _ _ [24,65,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9803 c9803
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9803_3
  · exact m9803_5
  · exact m9803_6
  · exact m9803_33
  · exact m9803_34
  · exact m9803_36

theorem m9804_3 : Upper (D 5) (R 5) [24,68,130,3] 13 :=
  permutation_upper _ _ _ [6,17,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8708

theorem m9804_5 : Upper (D 5) (R 5) [24,68,130,5] 13 :=
  permutation_upper _ _ _ [6,17,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8708

theorem m9804_6 : Upper (D 5) (R 5) [24,68,130,6] 13 :=
  permutation_upper _ _ _ [6,68,130,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9119

theorem m9804_33 : Upper (D 5) (R 5) [24,68,130,33] 13 :=
  permutation_upper _ _ _ [18,33,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9230

theorem m9804_34 : Upper (D 5) (R 5) [24,68,130,34] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9261

theorem m9804_36 : Upper (D 5) (R 5) [24,68,130,36] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9261

theorem m9804_257 : Upper (D 5) (R 5) [24,68,130,257] 13 :=
  permutation_upper _ _ _ [18,65,136,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9296

theorem m9804_258 : Upper (D 5) (R 5) [24,68,130,258] 13 :=
  permutation_upper _ _ _ [18,68,136,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9338

theorem m9804_260 : Upper (D 5) (R 5) [24,68,130,260] 13 :=
  permutation_upper _ _ _ [18,68,136,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9338

theorem m9804_288 : Upper (D 5) (R 5) [24,68,130,288] 13 :=
  permutation_upper _ _ _ [18,96,136,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9367

def r9804 : Route 9 := (fun mask => (mask,id))

def c9804 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9804 : Upper (D 5) (R 5) [24,68,130] 13 := by
  apply FastRouting.sound _ _ [24,68,130] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9804 c9804
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9804_3
  · exact m9804_5
  · exact m9804_6
  · exact m9804_33
  · exact m9804_34
  · exact m9804_36
  · exact m9804_257
  · exact m9804_258
  · exact m9804_260
  · exact m9804_288

theorem m9805_3 : Upper (D 5) (R 5) [24,68,160,3] 13 :=
  permutation_upper _ _ _ [6,17,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8709

theorem m9805_5 : Upper (D 5) (R 5) [24,68,160,5] 13 :=
  permutation_upper _ _ _ [6,17,96,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8717

theorem m9805_6 : Upper (D 5) (R 5) [24,68,160,6] 13 :=
  permutation_upper _ _ _ [6,68,160,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9139

theorem m9805_33 : Upper (D 5) (R 5) [24,68,160,33] 13 :=
  permutation_upper _ _ _ [18,33,72,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9231

theorem m9805_34 : Upper (D 5) (R 5) [24,68,160,34] 13 :=
  permutation_upper _ _ _ [18,36,72,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9262

theorem m9805_36 : Upper (D 5) (R 5) [24,68,160,36] 13 :=
  permutation_upper _ _ _ [18,36,96,132] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9265

theorem m9805_257 : Upper (D 5) (R 5) [24,68,160,257] 13 :=
  permutation_upper _ _ _ [18,65,136,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9297

theorem m9805_258 : Upper (D 5) (R 5) [24,68,160,258] 13 :=
  permutation_upper _ _ _ [18,68,136,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9339

theorem m9805_260 : Upper (D 5) (R 5) [24,68,160,260] 13 :=
  permutation_upper _ _ _ [18,68,160,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9345

theorem m9805_288 : Upper (D 5) (R 5) [24,68,160,288] 13 :=
  permutation_upper _ _ _ [18,96,136,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9368

def r9805 : Route 9 := (fun mask => (mask,id))

def c9805 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9805 : Upper (D 5) (R 5) [24,68,160] 13 := by
  apply FastRouting.sound _ _ [24,68,160] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9805 c9805
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9805_3
  · exact m9805_5
  · exact m9805_6
  · exact m9805_33
  · exact m9805_34
  · exact m9805_36
  · exact m9805_257
  · exact m9805_258
  · exact m9805_260
  · exact m9805_288

theorem m9806_3 : Upper (D 5) (R 5) [24,68,384,3] 13 :=
  permutation_upper _ _ _ [6,17,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8710

theorem m9806_5 : Upper (D 5) (R 5) [24,68,384,5] 13 :=
  permutation_upper _ _ _ [6,17,192,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8726

theorem m9806_6 : Upper (D 5) (R 5) [24,68,384,6] 13 :=
  permutation_upper _ _ _ [6,68,384,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9148

theorem m9806_33 : Upper (D 5) (R 5) [24,68,384,33] 13 :=
  permutation_upper _ _ _ [18,33,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9232

theorem m9806_34 : Upper (D 5) (R 5) [24,68,384,34] 13 :=
  permutation_upper _ _ _ [18,36,72,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9263

theorem m9806_36 : Upper (D 5) (R 5) [24,68,384,36] 13 :=
  permutation_upper _ _ _ [18,36,192,260] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9272

def r9806 : Route 9 := (fun mask => (mask,id))

def c9806 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9806 : Upper (D 5) (R 5) [24,68,384] 13 := by
  apply FastRouting.sound _ _ [24,68,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9806 c9806
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9806_3
  · exact m9806_5
  · exact m9806_6
  · exact m9806_33
  · exact m9806_34
  · exact m9806_36

theorem m9807_3 : Upper (D 5) (R 5) [24,96,160,3] 13 :=
  permutation_upper _ _ _ [6,17,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8718

theorem m9807_5 : Upper (D 5) (R 5) [24,96,160,5] 13 :=
  permutation_upper _ _ _ [6,17,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8718

theorem m9807_6 : Upper (D 5) (R 5) [24,96,160,6] 13 :=
  permutation_upper _ _ _ [6,96,160,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9200

theorem m9807_257 : Upper (D 5) (R 5) [24,96,160,257] 13 :=
  permutation_upper _ _ _ [18,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9298

theorem m9807_258 : Upper (D 5) (R 5) [24,96,160,258] 13 :=
  permutation_upper _ _ _ [18,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9346

theorem m9807_260 : Upper (D 5) (R 5) [24,96,160,260] 13 :=
  permutation_upper _ _ _ [18,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9346

def r9807 : Route 9 := (fun mask => (mask,id))

def c9807 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 129 => 7 | 18 => 4 | 34 => 5 | 66 => 6 | 130 => 7 | 20 => 4 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9807 : Upper (D 5) (R 5) [24,96,160] 13 := by
  apply FastRouting.sound _ _ [24,96,160] 13 (by decide) (choices 2) [3,5,6,257,258,260] r9807 c9807
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9807_3
  · exact m9807_5
  · exact m9807_6
  · exact m9807_257
  · exact m9807_258
  · exact m9807_260

theorem m9808_3 : Upper (D 5) (R 5) [24,96,384,3] 13 :=
  permutation_upper _ _ _ [6,17,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8719

theorem m9808_5 : Upper (D 5) (R 5) [24,96,384,5] 13 :=
  permutation_upper _ _ _ [6,17,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8727

theorem m9808_6 : Upper (D 5) (R 5) [24,96,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,17] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9206

theorem m9808_33 : Upper (D 5) (R 5) [24,96,384,33] 13 :=
  permutation_upper _ _ _ [18,33,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9233

theorem m9808_34 : Upper (D 5) (R 5) [24,96,384,34] 13 :=
  permutation_upper _ _ _ [18,36,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9266

theorem m9808_36 : Upper (D 5) (R 5) [24,96,384,36] 13 :=
  permutation_upper _ _ _ [18,36,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9273

def r9808 : Route 9 := (fun mask => (mask,id))

def c9808 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 257 => 8 | 18 => 4 | 66 => 6 | 130 => 7 | 258 => 8 | 20 => 4 | 68 => 6 | 132 => 7 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9808 : Upper (D 5) (R 5) [24,96,384] 13 := by
  apply FastRouting.sound _ _ [24,96,384] 13 (by decide) (choices 2) [3,5,6,33,34,36] r9808 c9808
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9808_3
  · exact m9808_5
  · exact m9808_6
  · exact m9808_33
  · exact m9808_34
  · exact m9808_36

def b9809 : PairBound 9 := { available := 414, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 69 414 414 446 478 414 414), lower := (rows 35 35 69 8 16 32 64 128 256), losses := [] }

theorem u9809 : Upper (D 5) (R 5) [34,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9810 : PairBound 9 := { available := 399, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 84 399 415 431 463 399 399), lower := (rows 35 35 84 8 16 32 64 128 256), losses := [] }

theorem u9810 : Upper (D 5) (R 5) [34,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9811 : PairBound 9 := { available := 287, camps := [{ cop := 5, region := 3, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 35 196 287 287 319 351 415 287), lower := (rows 35 35 196 8 16 32 64 128 256), losses := [] }

theorem u9811 : Upper (D 5) (R 5) [34,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9812 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 69 415 415 447 479 415 415), lower := (rows 35 38 69 8 16 32 64 128 256), losses := [] }

theorem u9812 : Upper (D 5) (R 5) [34,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9813 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 70 413 413 445 477 413 413), lower := (rows 35 38 70 8 16 32 64 128 256), losses := [] }

theorem u9813 : Upper (D 5) (R 5) [34,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9814 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 84 399 415 431 463 399 399), lower := (rows 35 38 84 8 16 32 64 128 256), losses := [] }

theorem u9814 : Upper (D 5) (R 5) [34,36,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9815 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 38 196 287 287 319 351 415 287), lower := (rows 35 38 196 8 16 32 64 128 256), losses := [] }

theorem u9815 : Upper (D 5) (R 5) [34,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9816 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 42 69 415 415 447 479 415 415), lower := (rows 35 42 69 8 16 32 64 128 256), losses := [] }

theorem u9816 : Upper (D 5) (R 5) [34,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9817 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 42 84 399 415 431 463 399 399), lower := (rows 35 42 84 8 16 32 64 128 256), losses := [] }

theorem u9817 : Upper (D 5) (R 5) [34,40,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9818 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 476, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 42 196 287 287 319 351 415 287), lower := (rows 35 42 196 8 16 32 64 128 256), losses := [] }

theorem u9818 : Upper (D 5) (R 5) [34,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9819 : PairBound 9 := { available := 399, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 69 399 415 431 463 399 399), lower := (rows 35 50 69 8 16 32 64 128 256), losses := [] }

theorem u9819 : Upper (D 5) (R 5) [34,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9820 : PairBound 9 := { available := 397, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 70 397 413 429 461 397 397), lower := (rows 35 50 70 8 16 32 64 128 256), losses := [] }

theorem u9820 : Upper (D 5) (R 5) [34,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9821 : PairBound 9 := { available := 271, camps := [{ cop := 0, region := 460, targets := 32 }], pairs := [(2,5),(3,5)], upper := (rows 35 50 196 271 287 303 335 399 271), lower := (rows 35 50 196 8 16 32 64 128 256), losses := [] }

theorem u9821 : Upper (D 5) (R 5) [34,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b9822 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 4, targets := 1 },{ cop := 0, region := 4, targets := 8 }], pairs := [(2,0),(2,3)], upper := (rows 35 67 38 413 413 445 477 413 413), lower := (rows 35 67 38 8 16 32 64 128 256), losses := [] }

theorem u9822 : Upper (D 5) (R 5) [34,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b9822
    (constants 5).1 (constants 5).2 (by decide +kernel)

theorem m9823_3 : Upper (D 5) (R 5) [34,65,40,3] 13 :=
  permutation_upper _ _ _ [6,36,66,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8924

theorem m9823_5 : Upper (D 5) (R 5) [34,65,40,5] 13 :=
  permutation_upper _ _ _ [6,33,40,68] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8838

theorem m9823_6 : Upper (D 5) (R 5) [34,65,40,6] 13 :=
  permutation_upper _ _ _ [6,33,72,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8870

theorem m9823_17 : Upper (D 5) (R 5) [34,65,40,17] 13 :=
  permutation_upper _ _ _ [18,36,66,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9250

theorem m9823_18 : Upper (D 5) (R 5) [34,65,40,18] 13 :=
  permutation_upper _ _ _ [18,68,34,33] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9307

theorem m9823_20 : Upper (D 5) (R 5) [34,65,40,20] 13 :=
  permutation_upper _ _ _ [18,33,40,68] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9221

def r9823 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9823 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9823 : Upper (D 5) (R 5) [34,65,40] 13 := by
  apply FastRouting.sound _ _ [34,65,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r9823 c9823
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9823_3
  · exact m9823_5
  · exact m9823_6
  · exact m9823_17
  · exact m9823_18
  · exact m9823_20
  · exact u9424
  · exact u9425
  · exact u9426
  · exact u9427
  · exact u9428

theorem m9824_3 : Upper (D 5) (R 5) [34,65,48,3] 13 :=
  permutation_upper _ _ _ [6,36,66,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8925

theorem m9824_5 : Upper (D 5) (R 5) [34,65,48,5] 13 :=
  permutation_upper _ _ _ [6,40,48,66] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8963

theorem m9824_6 : Upper (D 5) (R 5) [34,65,48,6] 13 :=
  permutation_upper _ _ _ [6,48,72,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9043

def r9824 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9824 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9824 : Upper (D 5) (R 5) [34,65,48] 13 := by
  apply FastRouting.sound _ _ [34,65,48] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9824 c9824
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9824_3
  · exact m9824_5
  · exact m9824_6
  · exact u9429
  · exact u9430
  · exact u9431
  · exact u9432

theorem m9825_6 : Upper (D 5) (R 5) [34,65,129,6] 13 :=
  permutation_upper _ _ _ [6,72,136,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9156

theorem m9825_18 : Upper (D 5) (R 5) [34,65,129,18] 13 :=
  permutation_upper _ _ _ [18,68,34,132] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9310

theorem m9825_20 : Upper (D 5) (R 5) [34,65,129,20] 13 :=
  permutation_upper _ _ _ [18,68,40,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9318

theorem m9825_34 : Upper (D 5) (R 5) [34,65,129,34] 13 :=
  permutation_upper _ _ _ [34,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9420

theorem m9825_36 : Upper (D 5) (R 5) [34,65,129,36] 13 :=
  permutation_upper _ _ _ [34,65,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9424

theorem m9825_48 : Upper (D 5) (R 5) [34,65,129,48] 13 :=
  permutation_upper _ _ _ [34,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9429

def r9825 : Route 9 := (fun mask => (mask,id))

def c9825 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9825 : Upper (D 5) (R 5) [34,65,129] 13 := by
  apply FastRouting.sound _ _ [34,65,129] 13 (by decide) (choices 2) [6,18,20,34,36,48,258,260,272,288] r9825 c9825
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9825_6
  · exact m9825_18
  · exact m9825_20
  · exact m9825_34
  · exact m9825_36
  · exact m9825_48
  · exact u9433
  · exact u9434
  · exact u9435
  · exact u9436

theorem m9826_5 : Upper (D 5) (R 5) [34,65,130,5] 13 :=
  permutation_upper _ _ _ [6,40,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8993

theorem m9826_17 : Upper (D 5) (R 5) [34,65,130,17] 13 :=
  permutation_upper _ _ _ [18,36,66,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9253

theorem m9826_20 : Upper (D 5) (R 5) [34,65,130,20] 13 :=
  permutation_upper _ _ _ [18,68,136,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9335

theorem m9826_33 : Upper (D 5) (R 5) [34,65,130,33] 13 :=
  permutation_upper _ _ _ [34,36,66,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9397

theorem m9826_36 : Upper (D 5) (R 5) [34,65,130,36] 13 :=
  permutation_upper _ _ _ [34,65,40,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9425

theorem m9826_48 : Upper (D 5) (R 5) [34,65,130,48] 13 :=
  permutation_upper _ _ _ [34,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9430

theorem m9826_257 : Upper (D 5) (R 5) [34,65,130,257] 13 :=
  permutation_upper _ _ _ [34,65,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9433

def r9826 : Route 9 := (fun mask => (mask,id))

def c9826 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9826 : Upper (D 5) (R 5) [34,65,130] 13 := by
  apply FastRouting.sound _ _ [34,65,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r9826 c9826
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9826_5
  · exact m9826_17
  · exact m9826_20
  · exact m9826_33
  · exact m9826_36
  · exact m9826_48
  · exact m9826_257
  · exact u9437
  · exact u9438
  · exact u9439

theorem m9827_3 : Upper (D 5) (R 5) [34,65,136,3] 13 :=
  permutation_upper _ _ _ [6,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8926

theorem m9827_5 : Upper (D 5) (R 5) [34,65,136,5] 13 :=
  permutation_upper _ _ _ [6,40,65,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8974

theorem m9827_6 : Upper (D 5) (R 5) [34,65,136,6] 13 :=
  permutation_upper _ _ _ [6,65,136,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9083

theorem m9827_17 : Upper (D 5) (R 5) [34,65,136,17] 13 :=
  permutation_upper _ _ _ [18,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9252

theorem m9827_18 : Upper (D 5) (R 5) [34,65,136,18] 13 :=
  permutation_upper _ _ _ [18,68,34,129] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9309

theorem m9827_20 : Upper (D 5) (R 5) [34,65,136,20] 13 :=
  permutation_upper _ _ _ [18,65,40,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9288

theorem m9827_33 : Upper (D 5) (R 5) [34,65,136,33] 13 :=
  permutation_upper _ _ _ [34,36,66,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9396

theorem m9827_34 : Upper (D 5) (R 5) [34,65,136,34] 13 :=
  permutation_upper _ _ _ [34,65,34,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9421

theorem m9827_36 : Upper (D 5) (R 5) [34,65,136,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9426

theorem m9827_48 : Upper (D 5) (R 5) [34,65,136,48] 13 :=
  permutation_upper _ _ _ [34,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9431

theorem m9827_257 : Upper (D 5) (R 5) [34,65,136,257] 13 :=
  permutation_upper _ _ _ [34,65,129,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9434

theorem m9827_258 : Upper (D 5) (R 5) [34,65,136,258] 13 :=
  permutation_upper _ _ _ [34,65,130,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9437

def r9827 : Route 9 := (fun mask => (mask,id))

def c9827 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9827 : Upper (D 5) (R 5) [34,65,136] 13 := by
  apply FastRouting.sound _ _ [34,65,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9827 c9827
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9827_3
  · exact m9827_5
  · exact m9827_6
  · exact m9827_17
  · exact m9827_18
  · exact m9827_20
  · exact m9827_33
  · exact m9827_34
  · exact m9827_36
  · exact m9827_48
  · exact m9827_257
  · exact m9827_258
  · exact u9440
  · exact u9441
  · exact u9442

theorem m9828_3 : Upper (D 5) (R 5) [34,65,144,3] 13 :=
  permutation_upper _ _ _ [6,36,66,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8927

theorem m9828_5 : Upper (D 5) (R 5) [34,65,144,5] 13 :=
  permutation_upper _ _ _ [6,40,80,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9002

theorem m9828_6 : Upper (D 5) (R 5) [34,65,144,6] 13 :=
  permutation_upper _ _ _ [6,72,144,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9163

theorem m9828_33 : Upper (D 5) (R 5) [34,65,144,33] 13 :=
  permutation_upper _ _ _ [34,36,66,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9398

theorem m9828_34 : Upper (D 5) (R 5) [34,65,144,34] 13 :=
  permutation_upper _ _ _ [34,65,34,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9422

theorem m9828_36 : Upper (D 5) (R 5) [34,65,144,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9427

theorem m9828_257 : Upper (D 5) (R 5) [34,65,144,257] 13 :=
  permutation_upper _ _ _ [34,65,129,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9435

theorem m9828_258 : Upper (D 5) (R 5) [34,65,144,258] 13 :=
  permutation_upper _ _ _ [34,65,130,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9438

theorem m9828_260 : Upper (D 5) (R 5) [34,65,144,260] 13 :=
  permutation_upper _ _ _ [34,65,136,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9441

def r9828 : Route 9 := (fun mask => (mask,id))

def c9828 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9828 : Upper (D 5) (R 5) [34,65,144] 13 := by
  apply FastRouting.sound _ _ [34,65,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9828 c9828
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9828_3
  · exact m9828_5
  · exact m9828_6
  · exact m9828_33
  · exact m9828_34
  · exact m9828_36
  · exact m9828_257
  · exact m9828_258
  · exact m9828_260
  · exact u9443

theorem m9829_3 : Upper (D 5) (R 5) [34,65,160,3] 13 :=
  permutation_upper _ _ _ [6,36,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8928

theorem m9829_5 : Upper (D 5) (R 5) [34,65,160,5] 13 :=
  permutation_upper _ _ _ [6,40,96,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9010

theorem m9829_6 : Upper (D 5) (R 5) [34,65,160,6] 13 :=
  permutation_upper _ _ _ [6,72,160,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9173

theorem m9829_17 : Upper (D 5) (R 5) [34,65,160,17] 13 :=
  permutation_upper _ _ _ [18,36,66,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9254

theorem m9829_18 : Upper (D 5) (R 5) [34,65,160,18] 13 :=
  permutation_upper _ _ _ [18,68,34,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9311

theorem m9829_20 : Upper (D 5) (R 5) [34,65,160,20] 13 :=
  permutation_upper _ _ _ [18,96,40,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9359

theorem m9829_257 : Upper (D 5) (R 5) [34,65,160,257] 13 :=
  permutation_upper _ _ _ [34,65,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9436

theorem m9829_258 : Upper (D 5) (R 5) [34,65,160,258] 13 :=
  permutation_upper _ _ _ [34,65,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9439

theorem m9829_260 : Upper (D 5) (R 5) [34,65,160,260] 13 :=
  permutation_upper _ _ _ [34,65,136,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9442

theorem m9829_272 : Upper (D 5) (R 5) [34,65,160,272] 13 :=
  permutation_upper _ _ _ [34,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9443

def r9829 : Route 9 := (fun mask => (mask,id))

def c9829 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9829 : Upper (D 5) (R 5) [34,65,160] 13 := by
  apply FastRouting.sound _ _ [34,65,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r9829 c9829
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9829_3
  · exact m9829_5
  · exact m9829_6
  · exact m9829_17
  · exact m9829_18
  · exact m9829_20
  · exact m9829_257
  · exact m9829_258
  · exact m9829_260
  · exact m9829_272

theorem m9830_3 : Upper (D 5) (R 5) [34,65,384,3] 13 :=
  permutation_upper _ _ _ [6,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8929

theorem m9830_5 : Upper (D 5) (R 5) [34,65,384,5] 13 :=
  permutation_upper _ _ _ [6,40,192,258] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9022

theorem m9830_6 : Upper (D 5) (R 5) [34,65,384,6] 13 :=
  permutation_upper _ _ _ [6,72,384,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9185

theorem m9830_17 : Upper (D 5) (R 5) [34,65,384,17] 13 :=
  permutation_upper _ _ _ [18,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9255

theorem m9830_18 : Upper (D 5) (R 5) [34,65,384,18] 13 :=
  permutation_upper _ _ _ [18,68,34,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9312

theorem m9830_20 : Upper (D 5) (R 5) [34,65,384,20] 13 :=
  permutation_upper _ _ _ [18,192,40,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9383

theorem m9830_33 : Upper (D 5) (R 5) [34,65,384,33] 13 :=
  permutation_upper _ _ _ [34,36,66,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9399

theorem m9830_34 : Upper (D 5) (R 5) [34,65,384,34] 13 :=
  permutation_upper _ _ _ [34,65,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9423

theorem m9830_36 : Upper (D 5) (R 5) [34,65,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9428

theorem m9830_48 : Upper (D 5) (R 5) [34,65,384,48] 13 :=
  permutation_upper _ _ _ [34,65,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9432

def r9830 : Route 9 := (fun mask => (mask,id))

def c9830 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9830 : Upper (D 5) (R 5) [34,65,384] 13 := by
  apply FastRouting.sound _ _ [34,65,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9830 c9830
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9830_3
  · exact m9830_5
  · exact m9830_6
  · exact m9830_17
  · exact m9830_18
  · exact m9830_20
  · exact m9830_33
  · exact m9830_34
  · exact m9830_36
  · exact m9830_48

theorem m9831_3 : Upper (D 5) (R 5) [34,68,40,3] 13 :=
  permutation_upper _ _ _ [6,36,72,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8932

theorem m9831_5 : Upper (D 5) (R 5) [34,68,40,5] 13 :=
  permutation_upper _ _ _ [6,33,40,66] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8837

theorem m9831_6 : Upper (D 5) (R 5) [34,68,40,6] 13 :=
  permutation_upper _ _ _ [6,33,66,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8857

theorem m9831_17 : Upper (D 5) (R 5) [34,68,40,17] 13 :=
  permutation_upper _ _ _ [18,36,72,33] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9256

theorem m9831_18 : Upper (D 5) (R 5) [34,68,40,18] 13 :=
  permutation_upper _ _ _ [18,68,33,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9300

theorem m9831_20 : Upper (D 5) (R 5) [34,68,40,20] 13 :=
  permutation_upper _ _ _ [18,33,40,66] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9220

theorem m9831_132 : Upper (D 5) (R 5) [34,68,40,132] 13 :=
  permutation_upper _ _ _ [34,65,40,129] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9424

def r9831 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9831 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 48 => 5 | 80 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9831 : Upper (D 5) (R 5) [34,68,40] 13 := by
  apply FastRouting.sound _ _ [34,68,40] 13 (by decide) (choices 2) [3,5,6,17,18,20,129,130,132,144,384] r9831 c9831
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9831_3
  · exact m9831_5
  · exact m9831_6
  · exact m9831_17
  · exact m9831_18
  · exact m9831_20
  · exact u9444
  · exact u9445
  · exact m9831_132
  · exact u9446
  · exact u9447

theorem m9832_3 : Upper (D 5) (R 5) [34,68,48,3] 13 :=
  permutation_upper _ _ _ [6,36,72,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8933

theorem m9832_5 : Upper (D 5) (R 5) [34,68,48,5] 13 :=
  permutation_upper _ _ _ [6,40,48,68] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8964

theorem m9832_6 : Upper (D 5) (R 5) [34,68,48,6] 13 :=
  permutation_upper _ _ _ [6,48,66,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9036

def r9832 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9832 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9832 : Upper (D 5) (R 5) [34,68,48] 13 := by
  apply FastRouting.sound _ _ [34,68,48] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9832 c9832
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9832_3
  · exact m9832_5
  · exact m9832_6
  · exact u9448
  · exact u9449
  · exact u9450
  · exact u9451

theorem m9833_3 : Upper (D 5) (R 5) [34,68,129,3] 13 :=
  permutation_upper _ _ _ [6,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8935

theorem m9833_5 : Upper (D 5) (R 5) [34,68,129,5] 13 :=
  permutation_upper _ _ _ [6,40,66,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8982

theorem m9833_6 : Upper (D 5) (R 5) [34,68,129,6] 13 :=
  permutation_upper _ _ _ [6,68,136,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9128

theorem m9833_17 : Upper (D 5) (R 5) [34,68,129,17] 13 :=
  permutation_upper _ _ _ [18,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9260

theorem m9833_18 : Upper (D 5) (R 5) [34,68,129,18] 13 :=
  permutation_upper _ _ _ [18,68,136,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9334

theorem m9833_20 : Upper (D 5) (R 5) [34,68,129,20] 13 :=
  permutation_upper _ _ _ [18,68,40,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9317

theorem m9833_33 : Upper (D 5) (R 5) [34,68,129,33] 13 :=
  permutation_upper _ _ _ [34,36,72,130] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9401

theorem m9833_36 : Upper (D 5) (R 5) [34,68,129,36] 13 :=
  permutation_upper _ _ _ [34,68,40,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9445

def r9833 : Route 9 := (fun mask => (mask,id))

def c9833 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9833 : Upper (D 5) (R 5) [34,68,129] 13 := by
  apply FastRouting.sound _ _ [34,68,129] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9833 c9833
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9833_3
  · exact m9833_5
  · exact m9833_6
  · exact m9833_17
  · exact m9833_18
  · exact m9833_20
  · exact m9833_33
  · exact u9452
  · exact m9833_36
  · exact u9453
  · exact u9454
  · exact u9455
  · exact u9456
  · exact u9457
  · exact u9458

theorem m9834_5 : Upper (D 5) (R 5) [34,68,130,5] 13 :=
  permutation_upper _ _ _ [6,40,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8994

theorem m9834_17 : Upper (D 5) (R 5) [34,68,130,17] 13 :=
  permutation_upper _ _ _ [18,36,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9261

theorem m9834_20 : Upper (D 5) (R 5) [34,68,130,20] 13 :=
  permutation_upper _ _ _ [18,68,130,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9329

theorem m9834_33 : Upper (D 5) (R 5) [34,68,130,33] 13 :=
  permutation_upper _ _ _ [34,36,72,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9402

def r9834 : Route 9 := (fun mask => (mask,id))

def c9834 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9834 : Upper (D 5) (R 5) [34,68,130] 13 := by
  apply FastRouting.sound _ _ [34,68,130] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r9834 c9834
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9834_5
  · exact m9834_17
  · exact m9834_20
  · exact m9834_33
  · exact u9459
  · exact u9460
  · exact u9461
  · exact u9462
  · exact u9463
  · exact u9464

theorem m9835_3 : Upper (D 5) (R 5) [34,68,136,3] 13 :=
  permutation_upper _ _ _ [6,36,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8934

theorem m9835_5 : Upper (D 5) (R 5) [34,68,136,5] 13 :=
  permutation_upper _ _ _ [6,40,65,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8975

theorem m9835_6 : Upper (D 5) (R 5) [34,68,136,6] 13 :=
  permutation_upper _ _ _ [6,65,130,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9071

theorem m9835_17 : Upper (D 5) (R 5) [34,68,136,17] 13 :=
  permutation_upper _ _ _ [18,36,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9259

theorem m9835_18 : Upper (D 5) (R 5) [34,68,136,18] 13 :=
  permutation_upper _ _ _ [18,68,129,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9322

theorem m9835_20 : Upper (D 5) (R 5) [34,68,136,20] 13 :=
  permutation_upper _ _ _ [18,65,40,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9287

theorem m9835_33 : Upper (D 5) (R 5) [34,68,136,33] 13 :=
  permutation_upper _ _ _ [34,36,72,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9400

theorem m9835_34 : Upper (D 5) (R 5) [34,68,136,34] 13 :=
  permutation_upper _ _ _ [34,68,129,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9452

theorem m9835_36 : Upper (D 5) (R 5) [34,68,136,36] 13 :=
  permutation_upper _ _ _ [34,65,40,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9425

def r9835 : Route 9 := (fun mask => (mask,id))

def c9835 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9835 : Upper (D 5) (R 5) [34,68,136] 13 := by
  apply FastRouting.sound _ _ [34,68,136] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r9835 c9835
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9835_3
  · exact m9835_5
  · exact m9835_6
  · exact m9835_17
  · exact m9835_18
  · exact m9835_20
  · exact m9835_33
  · exact m9835_34
  · exact m9835_36
  · exact u9465
  · exact u9466
  · exact u9467
  · exact u9468
  · exact u9469
  · exact u9470

theorem m9836_3 : Upper (D 5) (R 5) [34,68,144,3] 13 :=
  permutation_upper _ _ _ [6,36,72,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8936

theorem m9836_5 : Upper (D 5) (R 5) [34,68,144,5] 13 :=
  permutation_upper _ _ _ [6,40,80,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9003

theorem m9836_6 : Upper (D 5) (R 5) [34,68,144,6] 13 :=
  permutation_upper _ _ _ [6,68,144,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9135

theorem m9836_33 : Upper (D 5) (R 5) [34,68,144,33] 13 :=
  permutation_upper _ _ _ [34,36,72,144] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9403

def r9836 : Route 9 := (fun mask => (mask,id))

def c9836 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 129 => 7 | 18 => 4 | 66 => 6 | 130 => 7 | 20 => 4 | 68 => 6 | 132 => 7 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9836 : Upper (D 5) (R 5) [34,68,144] 13 := by
  apply FastRouting.sound _ _ [34,68,144] 13 (by decide) (choices 2) [3,5,6,33,34,36,257,258,260,288] r9836 c9836
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9836_3
  · exact m9836_5
  · exact m9836_6
  · exact m9836_33
  · exact u9471
  · exact u9472
  · exact u9473
  · exact u9474
  · exact u9475
  · exact u9476

theorem m9837_3 : Upper (D 5) (R 5) [34,68,160,3] 13 :=
  permutation_upper _ _ _ [6,36,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8937

theorem m9837_5 : Upper (D 5) (R 5) [34,68,160,5] 13 :=
  permutation_upper _ _ _ [6,40,96,132] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9011

theorem m9837_6 : Upper (D 5) (R 5) [34,68,160,6] 13 :=
  permutation_upper _ _ _ [6,68,160,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9142

theorem m9837_17 : Upper (D 5) (R 5) [34,68,160,17] 13 :=
  permutation_upper _ _ _ [18,36,72,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9262

theorem m9837_18 : Upper (D 5) (R 5) [34,68,160,18] 13 :=
  permutation_upper _ _ _ [18,68,160,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9341

theorem m9837_20 : Upper (D 5) (R 5) [34,68,160,20] 13 :=
  permutation_upper _ _ _ [18,96,40,130] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9358

def r9837 : Route 9 := (fun mask => (mask,id))

def c9837 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 48 => 5 | 80 => 6 | 144 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9837 : Upper (D 5) (R 5) [34,68,160] 13 := by
  apply FastRouting.sound _ _ [34,68,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,257,258,260,272] r9837 c9837
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9837_3
  · exact m9837_5
  · exact m9837_6
  · exact m9837_17
  · exact m9837_18
  · exact m9837_20
  · exact u9477
  · exact u9478
  · exact u9479
  · exact u9480

theorem m9838_3 : Upper (D 5) (R 5) [34,68,384,3] 13 :=
  permutation_upper _ _ _ [6,36,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8938

theorem m9838_5 : Upper (D 5) (R 5) [34,68,384,5] 13 :=
  permutation_upper _ _ _ [6,40,192,260] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9023

theorem m9838_6 : Upper (D 5) (R 5) [34,68,384,6] 13 :=
  permutation_upper _ _ _ [6,68,384,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9151

theorem m9838_17 : Upper (D 5) (R 5) [34,68,384,17] 13 :=
  permutation_upper _ _ _ [18,36,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9263

theorem m9838_18 : Upper (D 5) (R 5) [34,68,384,18] 13 :=
  permutation_upper _ _ _ [18,68,384,34] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9348

theorem m9838_20 : Upper (D 5) (R 5) [34,68,384,20] 13 :=
  permutation_upper _ _ _ [18,192,40,258] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9382

theorem m9838_33 : Upper (D 5) (R 5) [34,68,384,33] 13 :=
  permutation_upper _ _ _ [34,36,72,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9404

def r9838 : Route 9 := (fun mask => (mask,id))

def c9838 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9838 : Upper (D 5) (R 5) [34,68,384] 13 := by
  apply FastRouting.sound _ _ [34,68,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r9838 c9838
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9838_3
  · exact m9838_5
  · exact m9838_6
  · exact m9838_17
  · exact m9838_18
  · exact m9838_20
  · exact m9838_33
  · exact u9481
  · exact u9482
  · exact u9483

theorem m9839_3 : Upper (D 5) (R 5) [34,72,48,3] 13 :=
  permutation_upper _ _ _ [6,36,65,48] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8917

theorem m9839_5 : Upper (D 5) (R 5) [34,72,48,5] 13 :=
  permutation_upper _ _ _ [6,40,48,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8962

theorem m9839_6 : Upper (D 5) (R 5) [34,72,48,6] 13 :=
  permutation_upper _ _ _ [6,48,65,36] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9029

theorem m9839_129 : Upper (D 5) (R 5) [34,72,48,129] 13 :=
  permutation_upper _ _ _ [34,68,129,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9453

theorem m9839_130 : Upper (D 5) (R 5) [34,72,48,130] 13 :=
  permutation_upper _ _ _ [34,68,130,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9460

theorem m9839_132 : Upper (D 5) (R 5) [34,72,48,132] 13 :=
  permutation_upper _ _ _ [34,68,136,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9465

theorem m9839_384 : Upper (D 5) (R 5) [34,72,48,384] 13 :=
  permutation_upper _ _ _ [34,68,384,48] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u9483

def r9839 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9839 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 18 => 4 | 34 => 5 | 66 => 6 | 20 => 4 | 36 => 5 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9839 : Upper (D 5) (R 5) [34,72,48] 13 := by
  apply FastRouting.sound _ _ [34,72,48] 13 (by decide) (choices 2) [3,5,6,129,130,132,384] r9839 c9839
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9839_3
  · exact m9839_5
  · exact m9839_6
  · exact m9839_129
  · exact m9839_130
  · exact m9839_132
  · exact m9839_384

#print axioms u9839
end Delivery.IrregularNine14.P05
