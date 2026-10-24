import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0132
import IrregularNine14P09C0133
import IrregularNine14P09C0134
import IrregularNine14P09C0135
import IrregularNine14P09C0136
import IrregularNine14P09C0137
import IrregularNine14P09C0138
import IrregularNine14P09C0139
import IrregularNine14P09C0140
import IrregularNine14P09C0141
import IrregularNine14P09C0142
import IrregularNine14P09C0143

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m9420_3 : Upper (D 9) (R 9) [96,20,129,288,3] 13 :=
  permutation_upper _ _ _ [96,5,10,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7970

theorem m9420_9 : Upper (D 9) (R 9) [96,20,129,288,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8267

theorem m9420_10 : Upper (D 9) (R 9) [96,20,129,288,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8355

theorem m9420_65 : Upper (D 9) (R 9) [96,20,129,288,65] 13 :=
  permutation_upper _ _ _ [96,12,33,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8370

theorem m9420_66 : Upper (D 9) (R 9) [96,20,129,288,66] 13 :=
  permutation_upper _ _ _ [96,12,34,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8396

theorem m9420_72 : Upper (D 9) (R 9) [96,20,129,288,72] 13 :=
  permutation_upper _ _ _ [96,12,48,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8418

theorem m9420_129 : Upper (D 9) (R 9) [96,20,129,288,129] 13 :=
  permutation_upper _ _ _ [96,12,129,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8450

theorem m9420_130 : Upper (D 9) (R 9) [96,20,129,288,130] 13 :=
  permutation_upper _ _ _ [96,12,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8452

theorem m9420_136 : Upper (D 9) (R 9) [96,20,129,288,136] 13 :=
  permutation_upper _ _ _ [96,12,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8458

theorem m9420_192 : Upper (D 9) (R 9) [96,20,129,288,192] 13 :=
  permutation_upper _ _ _ [96,12,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8463

theorem m9420_257 : Upper (D 9) (R 9) [96,20,129,288,257] 13 :=
  permutation_upper _ _ _ [96,12,129,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8467

theorem m9420_258 : Upper (D 9) (R 9) [96,20,129,288,258] 13 :=
  permutation_upper _ _ _ [96,12,129,258,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8474

theorem m9420_264 : Upper (D 9) (R 9) [96,20,129,288,264] 13 :=
  permutation_upper _ _ _ [96,12,129,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8484

theorem m9420_320 : Upper (D 9) (R 9) [96,20,129,288,320] 13 :=
  permutation_upper _ _ _ [96,12,129,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8493

theorem m9420_384 : Upper (D 9) (R 9) [96,20,129,288,384] 13 :=
  permutation_upper _ _ _ [96,12,129,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8500

def r9420 : Route 9 := (fun mask => (mask,id))

def c9420 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9420 : Upper (D 9) (R 9) [96,20,129,288] 13 := by
  apply FastRouting.sound _ _ [96,20,129,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r9420 c9420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9420_3
  · exact m9420_9
  · exact m9420_10
  · exact m9420_65
  · exact m9420_66
  · exact m9420_72
  · exact m9420_129
  · exact m9420_130
  · exact m9420_136
  · exact m9420_192
  · exact m9420_257
  · exact m9420_258
  · exact m9420_264
  · exact m9420_320
  · exact m9420_384

theorem m9421_3 : Upper (D 9) (R 9) [96,20,129,384,3] 13 :=
  permutation_upper _ _ _ [96,5,10,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7971

theorem m9421_9 : Upper (D 9) (R 9) [96,20,129,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,18,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8316

theorem m9421_10 : Upper (D 9) (R 9) [96,20,129,384,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8356

theorem m9421_33 : Upper (D 9) (R 9) [96,20,129,384,33] 13 :=
  permutation_upper _ _ _ [96,12,33,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8371

theorem m9421_34 : Upper (D 9) (R 9) [96,20,129,384,34] 13 :=
  permutation_upper _ _ _ [96,12,34,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8397

theorem m9421_40 : Upper (D 9) (R 9) [96,20,129,384,40] 13 :=
  permutation_upper _ _ _ [96,12,48,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8419

theorem m9421_96 : Upper (D 9) (R 9) [96,20,129,384,96] 13 :=
  permutation_upper _ _ _ [96,12,96,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8440

theorem m9421_257 : Upper (D 9) (R 9) [96,20,129,384,257] 13 :=
  permutation_upper _ _ _ [96,12,129,257,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8468

theorem m9421_258 : Upper (D 9) (R 9) [96,20,129,384,258] 13 :=
  permutation_upper _ _ _ [96,12,129,258,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8475

theorem m9421_264 : Upper (D 9) (R 9) [96,20,129,384,264] 13 :=
  permutation_upper _ _ _ [96,12,129,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8485

theorem m9421_288 : Upper (D 9) (R 9) [96,20,129,384,288] 13 :=
  permutation_upper _ _ _ [96,12,129,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8494

def r9421 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9421 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9421 : Upper (D 9) (R 9) [96,20,129,384] 13 := by
  apply FastRouting.sound _ _ [96,20,129,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r9421 c9421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9421_3
  · exact m9421_9
  · exact m9421_10
  · exact m9421_33
  · exact m9421_34
  · exact m9421_40
  · exact m9421_96
  · exact m9421_257
  · exact m9421_258
  · exact m9421_264
  · exact m9421_288

theorem m9422_9 : Upper (D 9) (R 9) [96,20,130,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8102

theorem m9422_33 : Upper (D 9) (R 9) [96,20,130,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8372

theorem m9422_40 : Upper (D 9) (R 9) [96,20,130,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8421

theorem m9422_96 : Upper (D 9) (R 9) [96,20,130,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8441

theorem m9422_257 : Upper (D 9) (R 9) [96,20,130,129,257] 13 :=
  permutation_upper _ _ _ [96,12,129,258,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8473

theorem m9422_264 : Upper (D 9) (R 9) [96,20,130,129,264] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8507

theorem m9422_288 : Upper (D 9) (R 9) [96,20,130,129,288] 13 :=
  permutation_upper _ _ _ [96,12,130,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8513

def r9422 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9422 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9422 : Upper (D 9) (R 9) [96,20,130,129] 13 := by
  apply FastRouting.sound _ _ [96,20,130,129] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9422 c9422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9422_9
  · exact m9422_33
  · exact m9422_40
  · exact m9422_96
  · exact m9422_257
  · exact m9422_264
  · exact m9422_288

theorem m9423_9 : Upper (D 9) (R 9) [96,20,130,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8265

theorem m9423_65 : Upper (D 9) (R 9) [96,20,130,160,65] 13 :=
  permutation_upper _ _ _ [96,12,33,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8373

theorem m9423_72 : Upper (D 9) (R 9) [96,20,130,160,72] 13 :=
  permutation_upper _ _ _ [96,12,48,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8422

theorem m9423_257 : Upper (D 9) (R 9) [96,20,130,160,257] 13 :=
  permutation_upper _ _ _ [96,12,129,258,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8474

theorem m9423_264 : Upper (D 9) (R 9) [96,20,130,160,264] 13 :=
  permutation_upper _ _ _ [96,12,130,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8508

theorem m9423_320 : Upper (D 9) (R 9) [96,20,130,160,320] 13 :=
  permutation_upper _ _ _ [96,12,130,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8514

def r9423 : Route 9 := (fun mask => (mask,id))

def c9423 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9423 : Upper (D 9) (R 9) [96,20,130,160] 13 := by
  apply FastRouting.sound _ _ [96,20,130,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9423 c9423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9423_9
  · exact m9423_65
  · exact m9423_72
  · exact m9423_257
  · exact m9423_264
  · exact m9423_320

theorem m9424_9 : Upper (D 9) (R 9) [96,20,130,257,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8104

theorem m9424_33 : Upper (D 9) (R 9) [96,20,130,257,33] 13 :=
  permutation_upper _ _ _ [96,12,33,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8374

theorem m9424_40 : Upper (D 9) (R 9) [96,20,130,257,40] 13 :=
  permutation_upper _ _ _ [96,12,48,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8423

theorem m9424_96 : Upper (D 9) (R 9) [96,20,130,257,96] 13 :=
  permutation_upper _ _ _ [96,12,96,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8442

theorem m9424_129 : Upper (D 9) (R 9) [96,20,130,257,129] 13 :=
  permutation_upper _ _ _ [96,12,129,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8451

theorem m9424_136 : Upper (D 9) (R 9) [96,20,130,257,136] 13 :=
  permutation_upper _ _ _ [96,12,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8501

theorem m9424_160 : Upper (D 9) (R 9) [96,20,130,257,160] 13 :=
  permutation_upper _ _ _ [96,12,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8503

theorem m9424_257 : Upper (D 9) (R 9) [96,20,130,257,257] 13 :=
  permutation_upper _ _ _ [96,12,129,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8471

theorem m9424_264 : Upper (D 9) (R 9) [96,20,130,257,264] 13 :=
  permutation_upper _ _ _ [96,12,130,272,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8509

theorem m9424_288 : Upper (D 9) (R 9) [96,20,130,257,288] 13 :=
  permutation_upper _ _ _ [96,12,130,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8515

theorem m9424_384 : Upper (D 9) (R 9) [96,20,130,257,384] 13 :=
  permutation_upper _ _ _ [96,12,130,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8518

def r9424 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9424 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u9424 : Upper (D 9) (R 9) [96,20,130,257] 13 := by
  apply FastRouting.sound _ _ [96,20,130,257] 13 (by decide) (choices 2) [9,33,40,96,129,136,160,257,264,288,384] r9424 c9424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9424_9
  · exact m9424_33
  · exact m9424_40
  · exact m9424_96
  · exact m9424_129
  · exact m9424_136
  · exact m9424_160
  · exact m9424_257
  · exact m9424_264
  · exact m9424_288
  · exact m9424_384

theorem m9425_9 : Upper (D 9) (R 9) [96,20,130,288,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8268

theorem m9425_65 : Upper (D 9) (R 9) [96,20,130,288,65] 13 :=
  permutation_upper _ _ _ [96,12,33,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8375

theorem m9425_72 : Upper (D 9) (R 9) [96,20,130,288,72] 13 :=
  permutation_upper _ _ _ [96,12,48,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8424

theorem m9425_129 : Upper (D 9) (R 9) [96,20,130,288,129] 13 :=
  permutation_upper _ _ _ [96,12,129,130,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8452

theorem m9425_136 : Upper (D 9) (R 9) [96,20,130,288,136] 13 :=
  permutation_upper _ _ _ [96,12,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8502

theorem m9425_192 : Upper (D 9) (R 9) [96,20,130,288,192] 13 :=
  permutation_upper _ _ _ [96,12,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8504

theorem m9425_257 : Upper (D 9) (R 9) [96,20,130,288,257] 13 :=
  permutation_upper _ _ _ [96,12,129,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8472

theorem m9425_264 : Upper (D 9) (R 9) [96,20,130,288,264] 13 :=
  permutation_upper _ _ _ [96,12,130,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8510

theorem m9425_320 : Upper (D 9) (R 9) [96,20,130,288,320] 13 :=
  permutation_upper _ _ _ [96,12,130,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8516

theorem m9425_384 : Upper (D 9) (R 9) [96,20,130,288,384] 13 :=
  permutation_upper _ _ _ [96,12,130,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8519

def r9425 : Route 9 := (fun mask => (mask,id))

def c9425 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9425 : Upper (D 9) (R 9) [96,20,130,288] 13 := by
  apply FastRouting.sound _ _ [96,20,130,288] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9425 c9425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9425_9
  · exact m9425_65
  · exact m9425_72
  · exact m9425_129
  · exact m9425_136
  · exact m9425_192
  · exact m9425_257
  · exact m9425_264
  · exact m9425_320
  · exact m9425_384

theorem m9426_9 : Upper (D 9) (R 9) [96,20,130,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,18,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8317

theorem m9426_33 : Upper (D 9) (R 9) [96,20,130,384,33] 13 :=
  permutation_upper _ _ _ [96,12,33,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8376

theorem m9426_40 : Upper (D 9) (R 9) [96,20,130,384,40] 13 :=
  permutation_upper _ _ _ [96,12,48,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8425

theorem m9426_96 : Upper (D 9) (R 9) [96,20,130,384,96] 13 :=
  permutation_upper _ _ _ [96,12,96,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8443

theorem m9426_257 : Upper (D 9) (R 9) [96,20,130,384,257] 13 :=
  permutation_upper _ _ _ [96,12,129,258,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8475

theorem m9426_264 : Upper (D 9) (R 9) [96,20,130,384,264] 13 :=
  permutation_upper _ _ _ [96,12,130,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8511

theorem m9426_288 : Upper (D 9) (R 9) [96,20,130,384,288] 13 :=
  permutation_upper _ _ _ [96,12,130,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8517

def r9426 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9426 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9426 : Upper (D 9) (R 9) [96,20,130,384] 13 := by
  apply FastRouting.sound _ _ [96,20,130,384] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9426 c9426
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9426_9
  · exact m9426_33
  · exact m9426_40
  · exact m9426_96
  · exact m9426_257
  · exact m9426_264
  · exact m9426_288

theorem m9427_65 : Upper (D 9) (R 9) [96,20,136,34,65] 13 :=
  permutation_upper _ _ _ [96,12,33,144,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8377

theorem m9427_129 : Upper (D 9) (R 9) [96,20,136,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8454

theorem m9427_192 : Upper (D 9) (R 9) [96,20,136,34,192] 13 :=
  permutation_upper _ _ _ [96,12,144,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8521

theorem m9427_257 : Upper (D 9) (R 9) [96,20,136,34,257] 13 :=
  permutation_upper _ _ _ [96,12,129,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8477

theorem m9427_320 : Upper (D 9) (R 9) [96,20,136,34,320] 13 :=
  permutation_upper _ _ _ [96,12,144,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8526

theorem m9427_384 : Upper (D 9) (R 9) [96,20,136,34,384] 13 :=
  permutation_upper _ _ _ [96,12,144,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8535

def r9427 : Route 9 := (fun mask => (mask,id))

def c9427 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9427 : Upper (D 9) (R 9) [96,20,136,34] 13 := by
  apply FastRouting.sound _ _ [96,20,136,34] 13 (by decide) (choices 2) [65,129,192,257,320,384] r9427 c9427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9427_65
  · exact m9427_129
  · exact m9427_192
  · exact m9427_257
  · exact m9427_320
  · exact m9427_384

def b9428 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 22 140 137 371 355 355 483 355), lower := (rows 97 22 140 137 16 32 64 128 256), losses := [] }

theorem u9428 : Upper (D 9) (R 9) [96,20,136,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9428 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9429 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 22 140 138 369 353 353 481 353), lower := (rows 97 22 140 138 16 32 64 128 256), losses := [] }

theorem u9429 : Upper (D 9) (R 9) [96,20,136,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9429 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9430 : PairBound 9 := { available := 323, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 22 140 168 339 355 323 451 323), lower := (rows 97 22 140 168 16 32 64 128 256), losses := [] }

theorem u9430 : Upper (D 9) (R 9) [96,20,136,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9430 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9431_3 : Upper (D 9) (R 9) [96,20,136,257,3] 13 :=
  permutation_upper _ _ _ [96,5,10,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7976

theorem m9431_33 : Upper (D 9) (R 9) [96,20,136,257,33] 13 :=
  permutation_upper _ _ _ [96,12,33,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8378

theorem m9431_34 : Upper (D 9) (R 9) [96,20,136,257,34] 13 :=
  permutation_upper _ _ _ [96,12,34,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8401

theorem m9431_96 : Upper (D 9) (R 9) [96,20,136,257,96] 13 :=
  permutation_upper _ _ _ [96,12,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8444

theorem m9431_129 : Upper (D 9) (R 9) [96,20,136,257,129] 13 :=
  permutation_upper _ _ _ [96,12,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8456

theorem m9431_130 : Upper (D 9) (R 9) [96,20,136,257,130] 13 :=
  permutation_upper _ _ _ [96,12,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8501

theorem m9431_160 : Upper (D 9) (R 9) [96,20,136,257,160] 13 :=
  permutation_upper _ _ _ [96,12,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8522

theorem m9431_257 : Upper (D 9) (R 9) [96,20,136,257,257] 13 :=
  permutation_upper _ _ _ [96,12,129,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8479

theorem m9431_258 : Upper (D 9) (R 9) [96,20,136,257,258] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8507

theorem m9431_288 : Upper (D 9) (R 9) [96,20,136,257,288] 13 :=
  permutation_upper _ _ _ [96,12,144,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8530

theorem m9431_384 : Upper (D 9) (R 9) [96,20,136,257,384] 13 :=
  permutation_upper _ _ _ [96,12,144,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8537

def r9431 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9431 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9431 : Upper (D 9) (R 9) [96,20,136,257] 13 := by
  apply FastRouting.sound _ _ [96,20,136,257] 13 (by decide) (choices 2) [3,33,34,96,129,130,160,257,258,288,384] r9431 c9431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9431_3
  · exact m9431_33
  · exact m9431_34
  · exact m9431_96
  · exact m9431_129
  · exact m9431_130
  · exact m9431_160
  · exact m9431_257
  · exact m9431_258
  · exact m9431_288
  · exact m9431_384

theorem m9432_33 : Upper (D 9) (R 9) [96,20,136,258,33] 13 :=
  permutation_upper _ _ _ [96,12,33,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8379

theorem m9432_96 : Upper (D 9) (R 9) [96,20,136,258,96] 13 :=
  permutation_upper _ _ _ [96,12,96,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8445

theorem m9432_129 : Upper (D 9) (R 9) [96,20,136,258,129] 13 :=
  permutation_upper _ _ _ [96,12,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8457

theorem m9432_160 : Upper (D 9) (R 9) [96,20,136,258,160] 13 :=
  permutation_upper _ _ _ [96,12,144,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8523

theorem m9432_257 : Upper (D 9) (R 9) [96,20,136,258,257] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8480

theorem m9432_288 : Upper (D 9) (R 9) [96,20,136,258,288] 13 :=
  permutation_upper _ _ _ [96,12,144,288,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8531

theorem m9432_384 : Upper (D 9) (R 9) [96,20,136,258,384] 13 :=
  permutation_upper _ _ _ [96,12,144,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8538

def r9432 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9432 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u9432 : Upper (D 9) (R 9) [96,20,136,258] 13 := by
  apply FastRouting.sound _ _ [96,20,136,258] 13 (by decide) (choices 2) [33,96,129,160,257,288,384] r9432 c9432
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9432_33
  · exact m9432_96
  · exact m9432_129
  · exact m9432_160
  · exact m9432_257
  · exact m9432_288
  · exact m9432_384

theorem m9433_3 : Upper (D 9) (R 9) [96,20,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,10,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7977

theorem m9433_65 : Upper (D 9) (R 9) [96,20,136,288,65] 13 :=
  permutation_upper _ _ _ [96,12,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8380

theorem m9433_66 : Upper (D 9) (R 9) [96,20,136,288,66] 13 :=
  permutation_upper _ _ _ [96,12,34,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8402

theorem m9433_129 : Upper (D 9) (R 9) [96,20,136,288,129] 13 :=
  permutation_upper _ _ _ [96,12,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8458

theorem m9433_130 : Upper (D 9) (R 9) [96,20,136,288,130] 13 :=
  permutation_upper _ _ _ [96,12,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8502

theorem m9433_192 : Upper (D 9) (R 9) [96,20,136,288,192] 13 :=
  permutation_upper _ _ _ [96,12,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8524

theorem m9433_257 : Upper (D 9) (R 9) [96,20,136,288,257] 13 :=
  permutation_upper _ _ _ [96,12,129,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8481

theorem m9433_258 : Upper (D 9) (R 9) [96,20,136,288,258] 13 :=
  permutation_upper _ _ _ [96,12,130,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8508

theorem m9433_320 : Upper (D 9) (R 9) [96,20,136,288,320] 13 :=
  permutation_upper _ _ _ [96,12,144,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8532

theorem m9433_384 : Upper (D 9) (R 9) [96,20,136,288,384] 13 :=
  permutation_upper _ _ _ [96,12,144,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8539

def r9433 : Route 9 := (fun mask => (mask,id))

def c9433 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9433 : Upper (D 9) (R 9) [96,20,136,288] 13 := by
  apply FastRouting.sound _ _ [96,20,136,288] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r9433 c9433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9433_3
  · exact m9433_65
  · exact m9433_66
  · exact m9433_129
  · exact m9433_130
  · exact m9433_192
  · exact m9433_257
  · exact m9433_258
  · exact m9433_320
  · exact m9433_384

def b9434 : PairBound 9 := { available := 355, camps := [{ cop := 3, region := 4, targets := 353 },{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7),(2,0),(2,5),(2,6),(2,8)], upper := (rows 97 22 140 392 371 355 355 483 355), lower := (rows 97 22 140 392 16 32 64 128 256), losses := [] }

theorem u9434 : Upper (D 9) (R 9) [96,20,136,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9434 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9435_9 : Upper (D 9) (R 9) [96,20,160,66,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8047

theorem m9435_129 : Upper (D 9) (R 9) [96,20,160,66,129] 13 :=
  permutation_upper _ _ _ [96,12,129,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8460

theorem m9435_136 : Upper (D 9) (R 9) [96,20,160,66,136] 13 :=
  permutation_upper _ _ _ [96,12,144,160,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8521

theorem m9435_257 : Upper (D 9) (R 9) [96,20,160,66,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8487

theorem m9435_264 : Upper (D 9) (R 9) [96,20,160,66,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8526

theorem m9435_384 : Upper (D 9) (R 9) [96,20,160,66,384] 13 :=
  permutation_upper _ _ _ [96,12,160,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8546

def r9435 : Route 9 := (fun mask => (mask,id))

def c9435 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9435 : Upper (D 9) (R 9) [96,20,160,66] 13 := by
  apply FastRouting.sound _ _ [96,20,160,66] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9435 c9435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9435_9
  · exact m9435_129
  · exact m9435_136
  · exact m9435_257
  · exact m9435_264
  · exact m9435_384

theorem m9436_3 : Upper (D 9) (R 9) [96,20,160,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,160,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7980

theorem m9436_9 : Upper (D 9) (R 9) [96,20,160,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8103

theorem m9436_10 : Upper (D 9) (R 9) [96,20,160,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8353

theorem m9436_65 : Upper (D 9) (R 9) [96,20,160,129,65] 13 :=
  permutation_upper _ _ _ [96,12,33,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8381

theorem m9436_66 : Upper (D 9) (R 9) [96,20,160,129,66] 13 :=
  permutation_upper _ _ _ [96,12,34,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8404

theorem m9436_72 : Upper (D 9) (R 9) [96,20,160,129,72] 13 :=
  permutation_upper _ _ _ [96,12,48,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8426

theorem m9436_257 : Upper (D 9) (R 9) [96,20,160,129,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8491

theorem m9436_258 : Upper (D 9) (R 9) [96,20,160,129,258] 13 :=
  permutation_upper _ _ _ [96,12,130,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8515

theorem m9436_264 : Upper (D 9) (R 9) [96,20,160,129,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8530

theorem m9436_320 : Upper (D 9) (R 9) [96,20,160,129,320] 13 :=
  permutation_upper _ _ _ [96,12,160,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8542

def r9436 : Route 9 := (fun mask => (mask,id))

def c9436 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9436 : Upper (D 9) (R 9) [96,20,160,129] 13 := by
  apply FastRouting.sound _ _ [96,20,160,129] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r9436 c9436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9436_3
  · exact m9436_9
  · exact m9436_10
  · exact m9436_65
  · exact m9436_66
  · exact m9436_72
  · exact m9436_257
  · exact m9436_258
  · exact m9436_264
  · exact m9436_320

theorem m9437_9 : Upper (D 9) (R 9) [96,20,160,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8179

theorem m9437_65 : Upper (D 9) (R 9) [96,20,160,130,65] 13 :=
  permutation_upper _ _ _ [96,12,33,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8382

theorem m9437_72 : Upper (D 9) (R 9) [96,20,160,130,72] 13 :=
  permutation_upper _ _ _ [96,12,48,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8427

theorem m9437_257 : Upper (D 9) (R 9) [96,20,160,130,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8492

theorem m9437_264 : Upper (D 9) (R 9) [96,20,160,130,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8531

theorem m9437_320 : Upper (D 9) (R 9) [96,20,160,130,320] 13 :=
  permutation_upper _ _ _ [96,12,160,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8543

def r9437 : Route 9 := (fun mask => (mask,id))

def c9437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9437 : Upper (D 9) (R 9) [96,20,160,130] 13 := by
  apply FastRouting.sound _ _ [96,20,160,130] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9437 c9437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9437_9
  · exact m9437_65
  · exact m9437_72
  · exact m9437_257
  · exact m9437_264
  · exact m9437_320

theorem m9438_3 : Upper (D 9) (R 9) [96,20,160,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7981

theorem m9438_9 : Upper (D 9) (R 9) [96,20,160,192,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8266

theorem m9438_10 : Upper (D 9) (R 9) [96,20,160,192,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8357

theorem m9438_257 : Upper (D 9) (R 9) [96,20,160,192,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8493

theorem m9438_258 : Upper (D 9) (R 9) [96,20,160,192,258] 13 :=
  permutation_upper _ _ _ [96,12,130,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8516

theorem m9438_264 : Upper (D 9) (R 9) [96,20,160,192,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8532

def r9438 : Route 9 := (fun mask => (mask,id))

def c9438 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u9438 : Upper (D 9) (R 9) [96,20,160,192] 13 := by
  apply FastRouting.sound _ _ [96,20,160,192] 13 (by decide) (choices 2) [3,9,10,257,258,264] r9438 c9438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9438_3
  · exact m9438_9
  · exact m9438_10
  · exact m9438_257
  · exact m9438_258
  · exact m9438_264

theorem m9439_3 : Upper (D 9) (R 9) [96,20,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,10,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7982

theorem m9439_9 : Upper (D 9) (R 9) [96,20,160,257,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8105

theorem m9439_10 : Upper (D 9) (R 9) [96,20,160,257,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8355

theorem m9439_65 : Upper (D 9) (R 9) [96,20,160,257,65] 13 :=
  permutation_upper _ _ _ [96,12,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8383

theorem m9439_66 : Upper (D 9) (R 9) [96,20,160,257,66] 13 :=
  permutation_upper _ _ _ [96,12,34,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8405

theorem m9439_72 : Upper (D 9) (R 9) [96,20,160,257,72] 13 :=
  permutation_upper _ _ _ [96,12,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8428

theorem m9439_129 : Upper (D 9) (R 9) [96,20,160,257,129] 13 :=
  permutation_upper _ _ _ [96,12,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8461

theorem m9439_130 : Upper (D 9) (R 9) [96,20,160,257,130] 13 :=
  permutation_upper _ _ _ [96,12,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8503

theorem m9439_136 : Upper (D 9) (R 9) [96,20,160,257,136] 13 :=
  permutation_upper _ _ _ [96,12,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8522

theorem m9439_192 : Upper (D 9) (R 9) [96,20,160,257,192] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8540

theorem m9439_257 : Upper (D 9) (R 9) [96,20,160,257,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8488

theorem m9439_258 : Upper (D 9) (R 9) [96,20,160,257,258] 13 :=
  permutation_upper _ _ _ [96,12,130,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8513

theorem m9439_264 : Upper (D 9) (R 9) [96,20,160,257,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8527

theorem m9439_320 : Upper (D 9) (R 9) [96,20,160,257,320] 13 :=
  permutation_upper _ _ _ [96,12,160,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8542

theorem m9439_384 : Upper (D 9) (R 9) [96,20,160,257,384] 13 :=
  permutation_upper _ _ _ [96,12,160,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8547

def r9439 : Route 9 := (fun mask => (mask,id))

def c9439 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9439 : Upper (D 9) (R 9) [96,20,160,257] 13 := by
  apply FastRouting.sound _ _ [96,20,160,257] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r9439 c9439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9439_3
  · exact m9439_9
  · exact m9439_10
  · exact m9439_65
  · exact m9439_66
  · exact m9439_72
  · exact m9439_129
  · exact m9439_130
  · exact m9439_136
  · exact m9439_192
  · exact m9439_257
  · exact m9439_258
  · exact m9439_264
  · exact m9439_320
  · exact m9439_384

theorem m9440_9 : Upper (D 9) (R 9) [96,20,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8181

theorem m9440_65 : Upper (D 9) (R 9) [96,20,160,258,65] 13 :=
  permutation_upper _ _ _ [96,12,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8384

theorem m9440_72 : Upper (D 9) (R 9) [96,20,160,258,72] 13 :=
  permutation_upper _ _ _ [96,12,48,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8429

theorem m9440_129 : Upper (D 9) (R 9) [96,20,160,258,129] 13 :=
  permutation_upper _ _ _ [96,12,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8462

theorem m9440_136 : Upper (D 9) (R 9) [96,20,160,258,136] 13 :=
  permutation_upper _ _ _ [96,12,144,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8523

theorem m9440_192 : Upper (D 9) (R 9) [96,20,160,258,192] 13 :=
  permutation_upper _ _ _ [96,12,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8541

theorem m9440_257 : Upper (D 9) (R 9) [96,20,160,258,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8489

theorem m9440_264 : Upper (D 9) (R 9) [96,20,160,258,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8528

theorem m9440_320 : Upper (D 9) (R 9) [96,20,160,258,320] 13 :=
  permutation_upper _ _ _ [96,12,160,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8543

theorem m9440_384 : Upper (D 9) (R 9) [96,20,160,258,384] 13 :=
  permutation_upper _ _ _ [96,12,160,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8548

def r9440 : Route 9 := (fun mask => (mask,id))

def c9440 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9440 : Upper (D 9) (R 9) [96,20,160,258] 13 := by
  apply FastRouting.sound _ _ [96,20,160,258] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r9440 c9440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9440_9
  · exact m9440_65
  · exact m9440_72
  · exact m9440_129
  · exact m9440_136
  · exact m9440_192
  · exact m9440_257
  · exact m9440_264
  · exact m9440_320
  · exact m9440_384

theorem m9441_3 : Upper (D 9) (R 9) [96,20,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,10,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7983

theorem m9441_9 : Upper (D 9) (R 9) [96,20,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8269

theorem m9441_10 : Upper (D 9) (R 9) [96,20,160,320,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8358

theorem m9441_129 : Upper (D 9) (R 9) [96,20,160,320,129] 13 :=
  permutation_upper _ _ _ [96,12,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8463

theorem m9441_130 : Upper (D 9) (R 9) [96,20,160,320,130] 13 :=
  permutation_upper _ _ _ [96,12,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8504

theorem m9441_136 : Upper (D 9) (R 9) [96,20,160,320,136] 13 :=
  permutation_upper _ _ _ [96,12,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8524

theorem m9441_257 : Upper (D 9) (R 9) [96,20,160,320,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8490

theorem m9441_258 : Upper (D 9) (R 9) [96,20,160,320,258] 13 :=
  permutation_upper _ _ _ [96,12,130,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8514

theorem m9441_264 : Upper (D 9) (R 9) [96,20,160,320,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8529

theorem m9441_384 : Upper (D 9) (R 9) [96,20,160,320,384] 13 :=
  permutation_upper _ _ _ [96,12,160,384,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8549

def r9441 : Route 9 := (fun mask => (mask,id))

def c9441 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9441 : Upper (D 9) (R 9) [96,20,160,320] 13 := by
  apply FastRouting.sound _ _ [96,20,160,320] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r9441 c9441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9441_3
  · exact m9441_9
  · exact m9441_10
  · exact m9441_129
  · exact m9441_130
  · exact m9441_136
  · exact m9441_257
  · exact m9441_258
  · exact m9441_264
  · exact m9441_384

theorem m9442_3 : Upper (D 9) (R 9) [96,20,160,384,3] 13 :=
  permutation_upper _ _ _ [96,5,10,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7984

theorem m9442_9 : Upper (D 9) (R 9) [96,20,160,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,18,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8318

theorem m9442_10 : Upper (D 9) (R 9) [96,20,160,384,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8359

theorem m9442_65 : Upper (D 9) (R 9) [96,20,160,384,65] 13 :=
  permutation_upper _ _ _ [96,12,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8385

theorem m9442_66 : Upper (D 9) (R 9) [96,20,160,384,66] 13 :=
  permutation_upper _ _ _ [96,12,34,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8406

theorem m9442_72 : Upper (D 9) (R 9) [96,20,160,384,72] 13 :=
  permutation_upper _ _ _ [96,12,48,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8430

theorem m9442_257 : Upper (D 9) (R 9) [96,20,160,384,257] 13 :=
  permutation_upper _ _ _ [96,12,129,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8494

theorem m9442_258 : Upper (D 9) (R 9) [96,20,160,384,258] 13 :=
  permutation_upper _ _ _ [96,12,130,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8517

theorem m9442_264 : Upper (D 9) (R 9) [96,20,160,384,264] 13 :=
  permutation_upper _ _ _ [96,12,144,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8533

theorem m9442_320 : Upper (D 9) (R 9) [96,20,160,384,320] 13 :=
  permutation_upper _ _ _ [96,12,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8544

def r9442 : Route 9 := (fun mask => (mask,id))

def c9442 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9442 : Upper (D 9) (R 9) [96,20,160,384] 13 := by
  apply FastRouting.sound _ _ [96,20,160,384] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r9442 c9442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9442_3
  · exact m9442_9
  · exact m9442_10
  · exact m9442_65
  · exact m9442_66
  · exact m9442_72
  · exact m9442_257
  · exact m9442_258
  · exact m9442_264
  · exact m9442_320

theorem m9443_9 : Upper (D 9) (R 9) [96,20,384,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8048

theorem m9443_65 : Upper (D 9) (R 9) [96,20,384,34,65] 13 :=
  permutation_upper _ _ _ [96,12,33,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8386

theorem m9443_72 : Upper (D 9) (R 9) [96,20,384,34,72] 13 :=
  permutation_upper _ _ _ [96,12,48,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8432

theorem m9443_129 : Upper (D 9) (R 9) [96,20,384,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8496

theorem m9443_136 : Upper (D 9) (R 9) [96,20,384,34,136] 13 :=
  permutation_upper _ _ _ [96,12,144,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8535

theorem m9443_192 : Upper (D 9) (R 9) [96,20,384,34,192] 13 :=
  permutation_upper _ _ _ [96,12,160,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8546

theorem m9443_384 : Upper (D 9) (R 9) [96,20,384,34,384] 13 :=
  permutation_upper _ _ _ [96,12,384,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8550

def r9443 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9443 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u9443 : Upper (D 9) (R 9) [96,20,384,34] 13 := by
  apply FastRouting.sound _ _ [96,20,384,34] 13 (by decide) (choices 2) [9,65,72,129,136,192,384] r9443 c9443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9443_9
  · exact m9443_65
  · exact m9443_72
  · exact m9443_129
  · exact m9443_136
  · exact m9443_192
  · exact m9443_384

theorem m9444_3 : Upper (D 9) (R 9) [96,20,384,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7987

theorem m9444_9 : Upper (D 9) (R 9) [96,20,384,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8106

theorem m9444_10 : Upper (D 9) (R 9) [96,20,384,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8356

theorem m9444_33 : Upper (D 9) (R 9) [96,20,384,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8387

theorem m9444_34 : Upper (D 9) (R 9) [96,20,384,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8408

theorem m9444_40 : Upper (D 9) (R 9) [96,20,384,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8433

theorem m9444_96 : Upper (D 9) (R 9) [96,20,384,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8446

theorem m9444_257 : Upper (D 9) (R 9) [96,20,384,129,257] 13 :=
  permutation_upper _ _ _ [96,12,129,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8498

theorem m9444_258 : Upper (D 9) (R 9) [96,20,384,129,258] 13 :=
  permutation_upper _ _ _ [96,12,130,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8518

theorem m9444_264 : Upper (D 9) (R 9) [96,20,384,129,264] 13 :=
  permutation_upper _ _ _ [96,12,144,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8537

theorem m9444_288 : Upper (D 9) (R 9) [96,20,384,129,288] 13 :=
  permutation_upper _ _ _ [96,12,160,384,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8547

def r9444 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9444 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9444 : Upper (D 9) (R 9) [96,20,384,129] 13 := by
  apply FastRouting.sound _ _ [96,20,384,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,96,257,258,264,288] r9444 c9444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9444_3
  · exact m9444_9
  · exact m9444_10
  · exact m9444_33
  · exact m9444_34
  · exact m9444_40
  · exact m9444_96
  · exact m9444_257
  · exact m9444_258
  · exact m9444_264
  · exact m9444_288

theorem m9445_9 : Upper (D 9) (R 9) [96,20,384,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8182

theorem m9445_33 : Upper (D 9) (R 9) [96,20,384,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8388

theorem m9445_40 : Upper (D 9) (R 9) [96,20,384,130,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8434

theorem m9445_96 : Upper (D 9) (R 9) [96,20,384,130,96] 13 :=
  permutation_upper _ _ _ [96,12,96,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8447

theorem m9445_257 : Upper (D 9) (R 9) [96,20,384,130,257] 13 :=
  permutation_upper _ _ _ [96,12,129,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8499

theorem m9445_264 : Upper (D 9) (R 9) [96,20,384,130,264] 13 :=
  permutation_upper _ _ _ [96,12,144,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8538

theorem m9445_288 : Upper (D 9) (R 9) [96,20,384,130,288] 13 :=
  permutation_upper _ _ _ [96,12,160,384,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8548

def r9445 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 320 => (288,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c9445 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9445 : Upper (D 9) (R 9) [96,20,384,130] 13 := by
  apply FastRouting.sound _ _ [96,20,384,130] 13 (by decide) (choices 2) [9,33,40,96,257,264,288] r9445 c9445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9445_9
  · exact m9445_33
  · exact m9445_40
  · exact m9445_96
  · exact m9445_257
  · exact m9445_264
  · exact m9445_288

theorem m9446_3 : Upper (D 9) (R 9) [96,20,384,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u7988

theorem m9446_9 : Upper (D 9) (R 9) [96,20,384,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8270

theorem m9446_10 : Upper (D 9) (R 9) [96,20,384,160,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8359

theorem m9446_65 : Upper (D 9) (R 9) [96,20,384,160,65] 13 :=
  permutation_upper _ _ _ [96,12,33,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8389

theorem m9446_66 : Upper (D 9) (R 9) [96,20,384,160,66] 13 :=
  permutation_upper _ _ _ [96,12,34,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8409

theorem m9446_72 : Upper (D 9) (R 9) [96,20,384,160,72] 13 :=
  permutation_upper _ _ _ [96,12,48,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8435

theorem m9446_257 : Upper (D 9) (R 9) [96,20,384,160,257] 13 :=
  permutation_upper _ _ _ [96,12,129,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8500

theorem m9446_258 : Upper (D 9) (R 9) [96,20,384,160,258] 13 :=
  permutation_upper _ _ _ [96,12,130,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8519

theorem m9446_264 : Upper (D 9) (R 9) [96,20,384,160,264] 13 :=
  permutation_upper _ _ _ [96,12,144,384,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8539

theorem m9446_320 : Upper (D 9) (R 9) [96,20,384,160,320] 13 :=
  permutation_upper _ _ _ [96,12,160,384,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8549

def r9446 : Route 9 := (fun mask => (mask,id))

def c9446 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 2 | 34 => 5 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9446 : Upper (D 9) (R 9) [96,20,384,160] 13 := by
  apply FastRouting.sound _ _ [96,20,384,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,257,258,264,320] r9446 c9446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9446_3
  · exact m9446_9
  · exact m9446_10
  · exact m9446_65
  · exact m9446_66
  · exact m9446_72
  · exact m9446_257
  · exact m9446_258
  · exact m9446_264
  · exact m9446_320

def b9447 : PairBound 9 := { available := 107, camps := [{ cop := 2, region := 8, targets := 97 },{ cop := 3, region := 4, targets := 33 }], pairs := [(2,0),(2,5),(3,0),(3,5),(3,6)], upper := (rows 97 22 388 392 123 107 107 235 363), lower := (rows 97 22 388 392 16 32 64 128 256), losses := [] }

theorem u9447 : Upper (D 9) (R 9) [96,20,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9447 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9448 : PairBound 9 := { available := 412, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 137 412 444 476 412 412), lower := (rows 97 35 70 137 16 32 64 128 256), losses := [] }

theorem u9448 : Upper (D 9) (R 9) [96,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9448 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9449 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 140 409 441 473 409 409), lower := (rows 97 35 70 140 16 32 64 128 256), losses := [] }

theorem u9449 : Upper (D 9) (R 9) [96,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9449 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9450 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,7),(1,8),(2,5),(2,7),(2,8)], upper := (rows 97 35 70 392 413 445 477 413 413), lower := (rows 97 35 70 392 16 32 64 128 256), losses := [] }

theorem u9450 : Upper (D 9) (R 9) [96,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9450 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9451 : PairBound 9 := { available := 406, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 137 406 438 470 406 406), lower := (rows 97 35 76 137 16 32 64 128 256), losses := [] }

theorem u9451 : Upper (D 9) (R 9) [96,33,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9451 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9452 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 138 405 437 469 405 405), lower := (rows 97 35 76 138 16 32 64 128 256), losses := [] }

theorem u9452 : Upper (D 9) (R 9) [96,33,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9452 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9453 : PairBound 9 := { available := 403, camps := [{ cop := 1, region := 476, targets := 32 },{ cop := 0, region := 402, targets := 64 }], pairs := [(1,6),(2,5),(3,5),(4,5),(4,6)], upper := (rows 97 35 76 140 403 435 467 403 403), lower := (rows 97 35 76 140 16 32 64 128 256), losses := [] }

theorem u9453 : Upper (D 9) (R 9) [96,33,72,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9453 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9454 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 76 392 407 439 471 407 407), lower := (rows 97 35 76 392 16 32 64 128 256), losses := [] }

theorem u9454 : Upper (D 9) (R 9) [96,33,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9454 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9455 : PairBound 9 := { available := 348, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 138 348 380 348 476 348), lower := (rows 97 35 133 138 16 32 64 128 256), losses := [] }

theorem u9455 : Upper (D 9) (R 9) [96,33,129,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9455 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9456 : PairBound 9 := { available := 286, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 200 286 318 350 414 286), lower := (rows 97 35 133 200 16 32 64 128 256), losses := [] }

theorem u9456 : Upper (D 9) (R 9) [96,33,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9456 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9457 : PairBound 9 := { available := 476, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 266 476 508 476 476 476), lower := (rows 97 35 133 266 16 32 64 128 256), losses := [] }

theorem u9457 : Upper (D 9) (R 9) [96,33,129,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9457 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9458 : PairBound 9 := { available := 474, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 268 474 506 474 474 474), lower := (rows 97 35 133 268 16 32 64 128 256), losses := [] }

theorem u9458 : Upper (D 9) (R 9) [96,33,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9458 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9459 : PairBound 9 := { available := 414, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 328 414 446 478 414 414), lower := (rows 97 35 133 328 16 32 64 128 256), losses := [] }

theorem u9459 : Upper (D 9) (R 9) [96,33,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9459 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9460 : PairBound 9 := { available := 350, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 133 392 350 382 350 478 350), lower := (rows 97 35 133 392 16 32 64 128 256), losses := [] }

theorem u9460 : Upper (D 9) (R 9) [96,33,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9460 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9461 : PairBound 9 := { available := 285, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 200 285 317 349 413 285), lower := (rows 97 35 134 200 16 32 64 128 256), losses := [] }

theorem u9461 : Upper (D 9) (R 9) [96,33,130,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9461 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9462 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 268 473 505 473 473 473), lower := (rows 97 35 134 268 16 32 64 128 256), losses := [] }

theorem u9462 : Upper (D 9) (R 9) [96,33,130,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9462 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9463 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 328 413 445 477 413 413), lower := (rows 97 35 134 328 16 32 64 128 256), losses := [] }

theorem u9463 : Upper (D 9) (R 9) [96,33,130,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9463 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9464 : PairBound 9 := { available := 349, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 134 392 349 381 349 477 349), lower := (rows 97 35 134 392 16 32 64 128 256), losses := [] }

theorem u9464 : Upper (D 9) (R 9) [96,33,130,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9464 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9465 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 140 268 467 499 467 467 467), lower := (rows 97 35 140 268 16 32 64 128 256), losses := [] }

theorem u9465 : Upper (D 9) (R 9) [96,33,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9465 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9466 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 140 328 407 439 471 407 407), lower := (rows 97 35 140 328 16 32 64 128 256), losses := [] }

theorem u9466 : Upper (D 9) (R 9) [96,33,136,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9466 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9467 : PairBound 9 := { available := 287, camps := [{ cop := 0, region := 2, targets := 448 },{ cop := 1, region := 476, targets := 32 }], pairs := [(1,6),(1,7),(1,8),(2,5),(3,5)], upper := (rows 97 35 196 392 287 319 351 415 287), lower := (rows 97 35 196 392 16 32 64 128 256), losses := [] }

theorem u9467 : Upper (D 9) (R 9) [96,33,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9467 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9468 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 137 409 441 473 409 409), lower := (rows 97 38 70 137 16 32 64 128 256), losses := [] }

theorem u9468 : Upper (D 9) (R 9) [96,36,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9468 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b9469 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 6, targets := 384 },{ cop := 0, region := 6, targets := 1 }], pairs := [(1,0),(1,7),(1,8),(2,7),(2,8)], upper := (rows 97 38 70 392 409 441 473 409 409), lower := (rows 97 38 70 392 16 32 64 128 256), losses := [] }

theorem u9469 : Upper (D 9) (R 9) [96,36,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9469 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9470_3 : Upper (D 9) (R 9) [96,36,72,129,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8053

def r9470 : Route 9 := (fun mask => (mask,id))

def c9470 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9470 : Upper (D 9) (R 9) [96,36,72,129] 13 := by
  apply FastRouting.sound _ _ [96,36,72,129] 13 (by decide) (choices 2) [3,129,130,257,258,384] r9470 c9470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9470_3
  · exact u8610
  · exact u8611
  · exact u8612
  · exact u8613
  · exact u8614

def r9471 : Route 9 := (fun mask => (mask,id))

def c9471 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9471 : Upper (D 9) (R 9) [96,36,72,130] 13 := by
  apply FastRouting.sound _ _ [96,36,72,130] 13 (by decide) (choices 2) [129,257,384] r9471 c9471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u8615
  · exact u8616
  · exact u8617

theorem m9472_3 : Upper (D 9) (R 9) [96,36,72,144,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8054

def r9472 : Route 9 := (fun mask => (mask,id))

def c9472 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9472 : Upper (D 9) (R 9) [96,36,72,144] 13 := by
  apply FastRouting.sound _ _ [96,36,72,144] 13 (by decide) (choices 2) [3,129,130,257,258,384] r9472 c9472
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9472_3
  · exact u8618
  · exact u8619
  · exact u8620
  · exact u8621
  · exact u8622

theorem m9473_3 : Upper (D 9) (R 9) [96,36,72,384,3] 13 :=
  permutation_upper _ _ _ [96,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8055

def r9473 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9473 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 65 => 6 | 6 => 2 | 10 => 3 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9473 : Upper (D 9) (R 9) [96,36,72,384] 13 := by
  apply FastRouting.sound _ _ [96,36,72,384] 13 (by decide) (choices 2) [3,129,130,384] r9473 c9473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m9473_3
  · exact u8623
  · exact u8624
  · exact u8625

theorem m9474_3 : Upper (D 9) (R 9) [96,36,80,129,3] 13 :=
  permutation_upper _ _ _ [96,5,40,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8051

theorem m9474_9 : Upper (D 9) (R 9) [96,36,80,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8107

theorem m9474_10 : Upper (D 9) (R 9) [96,36,80,129,10] 13 :=
  permutation_upper _ _ _ [96,12,48,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8412

theorem m9474_129 : Upper (D 9) (R 9) [96,36,80,129,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8610

theorem m9474_130 : Upper (D 9) (R 9) [96,36,80,129,130] 13 :=
  permutation_upper _ _ _ [96,36,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8615

theorem m9474_136 : Upper (D 9) (R 9) [96,36,80,129,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8618

theorem m9474_257 : Upper (D 9) (R 9) [96,36,80,129,257] 13 :=
  permutation_upper _ _ _ [96,36,72,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8612

theorem m9474_258 : Upper (D 9) (R 9) [96,36,80,129,258] 13 :=
  permutation_upper _ _ _ [96,36,72,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8616

theorem m9474_264 : Upper (D 9) (R 9) [96,36,80,129,264] 13 :=
  permutation_upper _ _ _ [96,36,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8620

theorem m9474_384 : Upper (D 9) (R 9) [96,36,80,129,384] 13 :=
  permutation_upper _ _ _ [96,36,72,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8623

def r9474 : Route 9 := (fun mask => (mask,id))

def c9474 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9474 : Upper (D 9) (R 9) [96,36,80,129] 13 := by
  apply FastRouting.sound _ _ [96,36,80,129] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r9474 c9474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9474_3
  · exact m9474_9
  · exact m9474_10
  · exact m9474_129
  · exact m9474_130
  · exact m9474_136
  · exact m9474_257
  · exact m9474_258
  · exact m9474_264
  · exact m9474_384

theorem m9475_9 : Upper (D 9) (R 9) [96,36,80,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,48,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8196

theorem m9475_129 : Upper (D 9) (R 9) [96,36,80,130,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8611

theorem m9475_136 : Upper (D 9) (R 9) [96,36,80,130,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8619

theorem m9475_257 : Upper (D 9) (R 9) [96,36,80,130,257] 13 :=
  permutation_upper _ _ _ [96,36,72,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8613

theorem m9475_264 : Upper (D 9) (R 9) [96,36,80,130,264] 13 :=
  permutation_upper _ _ _ [96,36,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8621

theorem m9475_384 : Upper (D 9) (R 9) [96,36,80,130,384] 13 :=
  permutation_upper _ _ _ [96,36,72,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8624

def r9475 : Route 9 := (fun mask => (mask,id))

def c9475 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9475 : Upper (D 9) (R 9) [96,36,80,130] 13 := by
  apply FastRouting.sound _ _ [96,36,80,130] 13 (by decide) (choices 2) [9,129,136,257,264,384] r9475 c9475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9475_9
  · exact m9475_129
  · exact m9475_136
  · exact m9475_257
  · exact m9475_264
  · exact m9475_384

theorem m9476_3 : Upper (D 9) (R 9) [96,36,80,384,3] 13 :=
  permutation_upper _ _ _ [96,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8052

theorem m9476_9 : Upper (D 9) (R 9) [96,36,80,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,34,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8325

theorem m9476_10 : Upper (D 9) (R 9) [96,36,80,384,10] 13 :=
  permutation_upper _ _ _ [96,12,48,384,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8432

theorem m9476_129 : Upper (D 9) (R 9) [96,36,80,384,129] 13 :=
  permutation_upper _ _ _ [96,36,72,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8614

theorem m9476_130 : Upper (D 9) (R 9) [96,36,80,384,130] 13 :=
  permutation_upper _ _ _ [96,36,72,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8617

theorem m9476_136 : Upper (D 9) (R 9) [96,36,80,384,136] 13 :=
  permutation_upper _ _ _ [96,36,72,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8622

theorem m9476_384 : Upper (D 9) (R 9) [96,36,80,384,384] 13 :=
  permutation_upper _ _ _ [96,36,72,384,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8625

def r9476 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c9476 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9476 : Upper (D 9) (R 9) [96,36,80,384] 13 := by
  apply FastRouting.sound _ _ [96,36,80,384] 13 (by decide) (choices 2) [3,9,10,129,130,136,384] r9476 c9476
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9476_3
  · exact m9476_9
  · exact m9476_10
  · exact m9476_129
  · exact m9476_130
  · exact m9476_136
  · exact m9476_384

theorem m9477_3 : Upper (D 9) (R 9) [96,36,129,80,3] 13 :=
  permutation_upper _ _ _ [96,5,40,129,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8056

theorem m9477_9 : Upper (D 9) (R 9) [96,36,129,80,9] 13 :=
  permutation_upper _ _ _ [96,5,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8031

theorem m9477_10 : Upper (D 9) (R 9) [96,36,129,80,10] 13 :=
  permutation_upper _ _ _ [96,12,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8390

def r9477 : Route 9 := (fun mask => (mask,id))

def c9477 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u9477 : Upper (D 9) (R 9) [96,36,129,80] 13 := by
  apply FastRouting.sound _ _ [96,36,129,80] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r9477 c9477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9477_3
  · exact m9477_9
  · exact m9477_10
  · exact u8626
  · exact u8627
  · exact u8628
  · exact u8629
  · exact u8630
  · exact u8631
  · exact u8632

def b9478 : PairBound 9 := { available := 346, camps := [{ cop := 2, region := 8, targets := 352 },{ cop := 3, region := 4, targets := 96 }], pairs := [(2,5),(2,6),(3,5),(3,6),(3,8)], upper := (rows 97 38 133 137 346 378 346 474 346), lower := (rows 97 38 133 137 16 32 64 128 256), losses := [] }

theorem u9478 : Upper (D 9) (R 9) [96,36,129,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b9478 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m9479_9 : Upper (D 9) (R 9) [96,36,129,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8197

theorem m9479_65 : Upper (D 9) (R 9) [96,36,129,130,65] 13 :=
  permutation_upper _ _ _ [96,33,72,129,132] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8559

theorem m9479_72 : Upper (D 9) (R 9) [96,36,129,130,72] 13 :=
  permutation_upper _ _ _ [96,36,129,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8627

def r9479 : Route 9 := (fun mask => (mask,id))

def c9479 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u9479 : Upper (D 9) (R 9) [96,36,129,130] 13 := by
  apply FastRouting.sound _ _ [96,36,129,130] 13 (by decide) (choices 2) [9,65,72,257,264,320] r9479 c9479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9479_9
  · exact m9479_65
  · exact m9479_72
  · exact u8636
  · exact u8637
  · exact u8638

#print axioms u9479
end Delivery.IrregularNine14.P09
