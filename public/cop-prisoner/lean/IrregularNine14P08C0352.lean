import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0211
import IrregularNine14P08C0212
import IrregularNine14P08C0213
import IrregularNine14P08C0215
import IrregularNine14P08C0216
import IrregularNine14P08C0217
import IrregularNine14P08C0218
import IrregularNine14P08C0220
import IrregularNine14P08C0222
import IrregularNine14P08C0223
import IrregularNine14P08C0224
import IrregularNine14P08C0225
import IrregularNine14P08C0226
import IrregularNine14P08C0227
import IrregularNine14P08C0228
import IrregularNine14P08C0230
import IrregularNine14P08C0231
import IrregularNine14P08C0232

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m21120_33 : Upper (D 8) (R 8) [96,12,17,34,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12713

theorem m21120_65 : Upper (D 8) (R 8) [96,12,17,34,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12948

theorem m21120_96 : Upper (D 8) (R 8) [96,12,17,34,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13058

theorem m21120_129 : Upper (D 8) (R 8) [96,12,17,34,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13095

theorem m21120_160 : Upper (D 8) (R 8) [96,12,17,34,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13331

theorem m21120_192 : Upper (D 8) (R 8) [96,12,17,34,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13425

theorem m21120_257 : Upper (D 8) (R 8) [96,12,17,34,257] 13 :=
  permutation_upper _ _ _ [96,5,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13461

theorem m21120_288 : Upper (D 8) (R 8) [96,12,17,34,288] 13 :=
  permutation_upper _ _ _ [96,5,288,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13581

theorem m21120_320 : Upper (D 8) (R 8) [96,12,17,34,320] 13 :=
  permutation_upper _ _ _ [96,5,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13630

theorem m21120_384 : Upper (D 8) (R 8) [96,12,17,34,384] 13 :=
  permutation_upper _ _ _ [96,5,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13644

def r21120 : Route 9 := (fun mask => (mask,id))

def c21120 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21120 : Upper (D 8) (R 8) [96,12,17,34] 13 := by
  apply FastRouting.sound _ _ [96,12,17,34] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21120 c21120
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21120_33
  · exact m21120_65
  · exact m21120_96
  · exact m21120_129
  · exact m21120_160
  · exact m21120_192
  · exact m21120_257
  · exact m21120_288
  · exact m21120_320
  · exact m21120_384

def b21121 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 21 137 498 482 482 482 482), lower := (rows 97 14 21 137 16 32 64 128 256), losses := [] }

theorem u21121 : Upper (D 8) (R 8) [96,12,17,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21121 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21122_33 : Upper (D 8) (R 8) [96,12,17,130,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12714

theorem m21122_65 : Upper (D 8) (R 8) [96,12,17,130,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12949

theorem m21122_96 : Upper (D 8) (R 8) [96,12,17,130,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13059

theorem m21122_129 : Upper (D 8) (R 8) [96,12,17,130,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13096

theorem m21122_160 : Upper (D 8) (R 8) [96,12,17,130,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13336

theorem m21122_192 : Upper (D 8) (R 8) [96,12,17,130,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13427

theorem m21122_257 : Upper (D 8) (R 8) [96,12,17,130,257] 13 :=
  permutation_upper _ _ _ [96,5,257,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13462

theorem m21122_288 : Upper (D 8) (R 8) [96,12,17,130,288] 13 :=
  permutation_upper _ _ _ [96,5,288,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13586

theorem m21122_320 : Upper (D 8) (R 8) [96,12,17,130,320] 13 :=
  permutation_upper _ _ _ [96,5,320,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13632

theorem m21122_384 : Upper (D 8) (R 8) [96,12,17,130,384] 13 :=
  permutation_upper _ _ _ [96,5,384,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13649

def r21122 : Route 9 := (fun mask => (mask,id))

def c21122 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21122 : Upper (D 8) (R 8) [96,12,17,130] 13 := by
  apply FastRouting.sound _ _ [96,12,17,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21122 c21122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21122_33
  · exact m21122_65
  · exact m21122_96
  · exact m21122_129
  · exact m21122_160
  · exact m21122_192
  · exact m21122_257
  · exact m21122_288
  · exact m21122_320
  · exact m21122_384

theorem m21123_3 : Upper (D 8) (R 8) [96,12,17,160,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12507

theorem m21123_33 : Upper (D 8) (R 8) [96,12,17,160,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12715

theorem m21123_34 : Upper (D 8) (R 8) [96,12,17,160,34] 13 :=
  permutation_upper _ _ _ [96,5,40,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12813

theorem m21123_65 : Upper (D 8) (R 8) [96,12,17,160,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12950

theorem m21123_66 : Upper (D 8) (R 8) [96,12,17,160,66] 13 :=
  permutation_upper _ _ _ [96,5,72,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13002

theorem m21123_96 : Upper (D 8) (R 8) [96,12,17,160,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13060

theorem m21123_129 : Upper (D 8) (R 8) [96,12,17,160,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13097

theorem m21123_130 : Upper (D 8) (R 8) [96,12,17,160,130] 13 :=
  permutation_upper _ _ _ [96,5,136,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13201

theorem m21123_160 : Upper (D 8) (R 8) [96,12,17,160,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13337

theorem m21123_192 : Upper (D 8) (R 8) [96,12,17,160,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13428

theorem m21123_257 : Upper (D 8) (R 8) [96,12,17,160,257] 13 :=
  permutation_upper _ _ _ [96,5,257,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13463

theorem m21123_258 : Upper (D 8) (R 8) [96,12,17,160,258] 13 :=
  permutation_upper _ _ _ [96,5,264,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13512

theorem m21123_288 : Upper (D 8) (R 8) [96,12,17,160,288] 13 :=
  permutation_upper _ _ _ [96,5,288,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13587

theorem m21123_320 : Upper (D 8) (R 8) [96,12,17,160,320] 13 :=
  permutation_upper _ _ _ [96,5,320,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13633

theorem m21123_384 : Upper (D 8) (R 8) [96,12,17,160,384] 13 :=
  permutation_upper _ _ _ [96,5,384,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13650

def r21123 : Route 9 := (fun mask => (mask,id))

def c21123 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21123 : Upper (D 8) (R 8) [96,12,17,160] 13 := by
  apply FastRouting.sound _ _ [96,12,17,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r21123 c21123
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21123_3
  · exact m21123_33
  · exact m21123_34
  · exact m21123_65
  · exact m21123_66
  · exact m21123_96
  · exact m21123_129
  · exact m21123_130
  · exact m21123_160
  · exact m21123_192
  · exact m21123_257
  · exact m21123_258
  · exact m21123_288
  · exact m21123_320
  · exact m21123_384

theorem m21124_3 : Upper (D 8) (R 8) [96,12,17,192,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12508

theorem m21124_33 : Upper (D 8) (R 8) [96,12,17,192,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12716

theorem m21124_34 : Upper (D 8) (R 8) [96,12,17,192,34] 13 :=
  permutation_upper _ _ _ [96,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12814

theorem m21124_129 : Upper (D 8) (R 8) [96,12,17,192,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13098

theorem m21124_130 : Upper (D 8) (R 8) [96,12,17,192,130] 13 :=
  permutation_upper _ _ _ [96,5,136,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13202

theorem m21124_160 : Upper (D 8) (R 8) [96,12,17,192,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13338

theorem m21124_257 : Upper (D 8) (R 8) [96,12,17,192,257] 13 :=
  permutation_upper _ _ _ [96,5,257,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13464

theorem m21124_258 : Upper (D 8) (R 8) [96,12,17,192,258] 13 :=
  permutation_upper _ _ _ [96,5,264,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13513

theorem m21124_288 : Upper (D 8) (R 8) [96,12,17,192,288] 13 :=
  permutation_upper _ _ _ [96,5,288,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13588

theorem m21124_384 : Upper (D 8) (R 8) [96,12,17,192,384] 13 :=
  permutation_upper _ _ _ [96,5,384,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13651

def r21124 : Route 9 := (fun mask => (mask,id))

def c21124 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21124 : Upper (D 8) (R 8) [96,12,17,192] 13 := by
  apply FastRouting.sound _ _ [96,12,17,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21124 c21124
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21124_3
  · exact m21124_33
  · exact m21124_34
  · exact m21124_129
  · exact m21124_130
  · exact m21124_160
  · exact m21124_257
  · exact m21124_258
  · exact m21124_288
  · exact m21124_384

def b21125 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 97 14 21 265 242 226 226 226 482), lower := (rows 97 14 21 265 16 32 64 128 256), losses := [] }

theorem u21125 : Upper (D 8) (R 8) [96,12,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21126_33 : Upper (D 8) (R 8) [96,12,17,258,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12717

theorem m21126_65 : Upper (D 8) (R 8) [96,12,17,258,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12951

theorem m21126_96 : Upper (D 8) (R 8) [96,12,17,258,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13061

theorem m21126_129 : Upper (D 8) (R 8) [96,12,17,258,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13099

theorem m21126_160 : Upper (D 8) (R 8) [96,12,17,258,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13340

theorem m21126_192 : Upper (D 8) (R 8) [96,12,17,258,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13430

def r21126 : Route 9 := (fun mask => (mask,id))

def c21126 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21126 : Upper (D 8) (R 8) [96,12,17,258] 13 := by
  apply FastRouting.sound _ _ [96,12,17,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21126 c21126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21126_33
  · exact m21126_65
  · exact m21126_96
  · exact m21126_129
  · exact m21126_160
  · exact m21126_192

theorem m21127_3 : Upper (D 8) (R 8) [96,12,17,288,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12509

theorem m21127_33 : Upper (D 8) (R 8) [96,12,17,288,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12718

theorem m21127_34 : Upper (D 8) (R 8) [96,12,17,288,34] 13 :=
  permutation_upper _ _ _ [96,5,40,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12816

theorem m21127_65 : Upper (D 8) (R 8) [96,12,17,288,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12952

theorem m21127_66 : Upper (D 8) (R 8) [96,12,17,288,66] 13 :=
  permutation_upper _ _ _ [96,5,72,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13004

theorem m21127_96 : Upper (D 8) (R 8) [96,12,17,288,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13062

theorem m21127_129 : Upper (D 8) (R 8) [96,12,17,288,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13100

theorem m21127_130 : Upper (D 8) (R 8) [96,12,17,288,130] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13204

theorem m21127_160 : Upper (D 8) (R 8) [96,12,17,288,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13341

theorem m21127_192 : Upper (D 8) (R 8) [96,12,17,288,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13431

def r21127 : Route 9 := (fun mask => (mask,id))

def c21127 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21127 : Upper (D 8) (R 8) [96,12,17,288] 13 := by
  apply FastRouting.sound _ _ [96,12,17,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21127 c21127
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21127_3
  · exact m21127_33
  · exact m21127_34
  · exact m21127_65
  · exact m21127_66
  · exact m21127_96
  · exact m21127_129
  · exact m21127_130
  · exact m21127_160
  · exact m21127_192

theorem m21128_3 : Upper (D 8) (R 8) [96,12,17,320,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12510

theorem m21128_33 : Upper (D 8) (R 8) [96,12,17,320,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12719

theorem m21128_34 : Upper (D 8) (R 8) [96,12,17,320,34] 13 :=
  permutation_upper _ _ _ [96,5,40,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12817

theorem m21128_129 : Upper (D 8) (R 8) [96,12,17,320,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13101

theorem m21128_130 : Upper (D 8) (R 8) [96,12,17,320,130] 13 :=
  permutation_upper _ _ _ [96,5,136,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13205

theorem m21128_160 : Upper (D 8) (R 8) [96,12,17,320,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13342

def r21128 : Route 9 := (fun mask => (mask,id))

def c21128 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21128 : Upper (D 8) (R 8) [96,12,17,320] 13 := by
  apply FastRouting.sound _ _ [96,12,17,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21128 c21128
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21128_3
  · exact m21128_33
  · exact m21128_34
  · exact m21128_129
  · exact m21128_130
  · exact m21128_160

theorem m21129_3 : Upper (D 8) (R 8) [96,12,17,384,3] 13 :=
  permutation_upper _ _ _ [96,5,9,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12511

theorem m21129_33 : Upper (D 8) (R 8) [96,12,17,384,33] 13 :=
  permutation_upper _ _ _ [96,5,33,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12720

theorem m21129_34 : Upper (D 8) (R 8) [96,12,17,384,34] 13 :=
  permutation_upper _ _ _ [96,5,40,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12818

theorem m21129_65 : Upper (D 8) (R 8) [96,12,17,384,65] 13 :=
  permutation_upper _ _ _ [96,5,65,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12953

theorem m21129_66 : Upper (D 8) (R 8) [96,12,17,384,66] 13 :=
  permutation_upper _ _ _ [96,5,72,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13005

theorem m21129_96 : Upper (D 8) (R 8) [96,12,17,384,96] 13 :=
  permutation_upper _ _ _ [96,5,96,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13063

theorem m21129_129 : Upper (D 8) (R 8) [96,12,17,384,129] 13 :=
  permutation_upper _ _ _ [96,5,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13102

theorem m21129_130 : Upper (D 8) (R 8) [96,12,17,384,130] 13 :=
  permutation_upper _ _ _ [96,5,136,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13206

theorem m21129_160 : Upper (D 8) (R 8) [96,12,17,384,160] 13 :=
  permutation_upper _ _ _ [96,5,160,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13343

theorem m21129_192 : Upper (D 8) (R 8) [96,12,17,384,192] 13 :=
  permutation_upper _ _ _ [96,5,192,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13432

def r21129 : Route 9 := (fun mask => (mask,id))

def c21129 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21129 : Upper (D 8) (R 8) [96,12,17,384] 13 := by
  apply FastRouting.sound _ _ [96,12,17,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21129 c21129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21129_3
  · exact m21129_33
  · exact m21129_34
  · exact m21129_65
  · exact m21129_66
  · exact m21129_96
  · exact m21129_129
  · exact m21129_130
  · exact m21129_160
  · exact m21129_192

def b21130 : PairBound 9 := { available := 481, camps := [{ cop := 0, region := 8, targets := 64 }], pairs := [(3,6)], upper := (rows 97 14 22 41 497 481 481 481 481), lower := (rows 97 14 22 41 16 32 64 128 256), losses := [] }

theorem u21130 : Upper (D 8) (R 8) [96,12,18,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21130 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21131 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 22 73 433 417 481 417 417), lower := (rows 97 14 22 73 16 32 64 128 256), losses := [] }

theorem u21131 : Upper (D 8) (R 8) [96,12,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21132 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 22 104 433 417 481 417 417), lower := (rows 97 14 22 104 16 32 64 128 256), losses := [] }

theorem u21132 : Upper (D 8) (R 8) [96,12,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21133_33 : Upper (D 8) (R 8) [96,12,18,129,33] 13 :=
  permutation_upper _ _ _ [96,12,18,33,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13689

theorem m21133_65 : Upper (D 8) (R 8) [96,12,18,129,65] 13 :=
  permutation_upper _ _ _ [96,12,18,65,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13694

theorem m21133_96 : Upper (D 8) (R 8) [96,12,18,129,96] 13 :=
  permutation_upper _ _ _ [96,12,18,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13699

def r21133 : Route 9 := (fun mask => (mask,id))

def c21133 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21133 : Upper (D 8) (R 8) [96,12,18,129] 13 := by
  apply FastRouting.sound _ _ [96,12,18,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21133 c21133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21133_33
  · exact m21133_65
  · exact m21133_96
  · exact u13704
  · exact u13705
  · exact u13706
  · exact u13707
  · exact u13708
  · exact u13709
  · exact u13710

theorem m21134_33 : Upper (D 8) (R 8) [96,12,18,160,33] 13 :=
  permutation_upper _ _ _ [96,12,18,33,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13690

theorem m21134_65 : Upper (D 8) (R 8) [96,12,18,160,65] 13 :=
  permutation_upper _ _ _ [96,12,18,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13695

theorem m21134_96 : Upper (D 8) (R 8) [96,12,18,160,96] 13 :=
  permutation_upper _ _ _ [96,12,18,96,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13700

theorem m21134_129 : Upper (D 8) (R 8) [96,12,18,160,129] 13 :=
  permutation_upper _ _ _ [96,12,18,129,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13705

def r21134 : Route 9 := (fun mask => (mask,id))

def c21134 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21134 : Upper (D 8) (R 8) [96,12,18,160] 13 := by
  apply FastRouting.sound _ _ [96,12,18,160] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21134 c21134
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21134_33
  · exact m21134_65
  · exact m21134_96
  · exact m21134_129
  · exact u13711
  · exact u13712
  · exact u13713
  · exact u13714
  · exact u13715
  · exact u13716

def b21135 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 22 200 433 417 481 417 417), lower := (rows 97 14 22 200 16 32 64 128 256), losses := [] }

theorem u21135 : Upper (D 8) (R 8) [96,12,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21135 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21136_33 : Upper (D 8) (R 8) [96,12,18,257,33] 13 :=
  permutation_upper _ _ _ [96,12,18,33,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13691

theorem m21136_65 : Upper (D 8) (R 8) [96,12,18,257,65] 13 :=
  permutation_upper _ _ _ [96,12,18,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13696

theorem m21136_96 : Upper (D 8) (R 8) [96,12,18,257,96] 13 :=
  permutation_upper _ _ _ [96,12,18,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13701

theorem m21136_129 : Upper (D 8) (R 8) [96,12,18,257,129] 13 :=
  permutation_upper _ _ _ [96,12,18,129,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13707

theorem m21136_160 : Upper (D 8) (R 8) [96,12,18,257,160] 13 :=
  permutation_upper _ _ _ [96,12,18,160,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13713

theorem m21136_192 : Upper (D 8) (R 8) [96,12,18,257,192] 13 :=
  permutation_upper _ _ _ [96,12,18,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13717

def r21136 : Route 9 := (fun mask => (mask,id))

def c21136 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21136 : Upper (D 8) (R 8) [96,12,18,257] 13 := by
  apply FastRouting.sound _ _ [96,12,18,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21136 c21136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21136_33
  · exact m21136_65
  · exact m21136_96
  · exact m21136_129
  · exact m21136_160
  · exact m21136_192

theorem m21137_33 : Upper (D 8) (R 8) [96,12,18,288,33] 13 :=
  permutation_upper _ _ _ [96,12,18,33,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13692

theorem m21137_65 : Upper (D 8) (R 8) [96,12,18,288,65] 13 :=
  permutation_upper _ _ _ [96,12,18,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13697

theorem m21137_96 : Upper (D 8) (R 8) [96,12,18,288,96] 13 :=
  permutation_upper _ _ _ [96,12,18,96,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13702

theorem m21137_129 : Upper (D 8) (R 8) [96,12,18,288,129] 13 :=
  permutation_upper _ _ _ [96,12,18,129,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13708

theorem m21137_160 : Upper (D 8) (R 8) [96,12,18,288,160] 13 :=
  permutation_upper _ _ _ [96,12,18,160,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13714

theorem m21137_192 : Upper (D 8) (R 8) [96,12,18,288,192] 13 :=
  permutation_upper _ _ _ [96,12,18,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13718

def r21137 : Route 9 := (fun mask => (mask,id))

def c21137 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21137 : Upper (D 8) (R 8) [96,12,18,288] 13 := by
  apply FastRouting.sound _ _ [96,12,18,288] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21137 c21137
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21137_33
  · exact m21137_65
  · exact m21137_96
  · exact m21137_129
  · exact m21137_160
  · exact m21137_192

def b21138 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 22 328 177 161 225 161 417), lower := (rows 97 14 22 328 16 32 64 128 256), losses := [] }

theorem u21138 : Upper (D 8) (R 8) [96,12,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21139_33 : Upper (D 8) (R 8) [96,12,18,384,33] 13 :=
  permutation_upper _ _ _ [96,12,18,33,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13693

theorem m21139_65 : Upper (D 8) (R 8) [96,12,18,384,65] 13 :=
  permutation_upper _ _ _ [96,12,18,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13698

theorem m21139_96 : Upper (D 8) (R 8) [96,12,18,384,96] 13 :=
  permutation_upper _ _ _ [96,12,18,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13703

theorem m21139_129 : Upper (D 8) (R 8) [96,12,18,384,129] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13710

theorem m21139_160 : Upper (D 8) (R 8) [96,12,18,384,160] 13 :=
  permutation_upper _ _ _ [96,12,18,160,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13716

theorem m21139_192 : Upper (D 8) (R 8) [96,12,18,384,192] 13 :=
  permutation_upper _ _ _ [96,12,18,192,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13719

def r21139 : Route 9 := (fun mask => (mask,id))

def c21139 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21139 : Upper (D 8) (R 8) [96,12,18,384] 13 := by
  apply FastRouting.sound _ _ [96,12,18,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21139 c21139
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21139_33
  · exact m21139_65
  · exact m21139_96
  · exact m21139_129
  · exact m21139_160
  · exact m21139_192

def b21140 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 37 42 465 497 465 465 465), lower := (rows 97 14 37 42 16 32 64 128 256), losses := [] }

theorem u21140 : Upper (D 8) (R 8) [96,12,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21140 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21141 : PairBound 9 := { available := 451, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 56 467 483 451 451 451), lower := (rows 97 14 37 56 16 32 64 128 256), losses := [] }

theorem u21141 : Upper (D 8) (R 8) [96,12,33,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21141 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21142 : PairBound 9 := { available := 419, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 88 435 419 483 419 419), lower := (rows 97 14 37 88 16 32 64 128 256), losses := [] }

theorem u21142 : Upper (D 8) (R 8) [96,12,33,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21142 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21143 : PairBound 9 := { available := 498, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 137 498 498 498 498 498), lower := (rows 97 14 37 137 16 32 64 128 256), losses := [] }

theorem u21143 : Upper (D 8) (R 8) [96,12,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21143 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21144 : PairBound 9 := { available := 497, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 138 497 497 497 497 497), lower := (rows 97 14 37 138 16 32 64 128 256), losses := [] }

theorem u21144 : Upper (D 8) (R 8) [96,12,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21144 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21145 : PairBound 9 := { available := 483, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 152 499 483 483 483 483), lower := (rows 97 14 37 152 16 32 64 128 256), losses := [] }

theorem u21145 : Upper (D 8) (R 8) [96,12,33,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21145 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21146 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 168 467 499 467 467 467), lower := (rows 97 14 37 168 16 32 64 128 256), losses := [] }

theorem u21146 : Upper (D 8) (R 8) [96,12,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21146 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21147 : PairBound 9 := { available := 435, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 200 435 435 499 435 435), lower := (rows 97 14 37 200 16 32 64 128 256), losses := [] }

theorem u21147 : Upper (D 8) (R 8) [96,12,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21147 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21148 : PairBound 9 := { available := 242, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 265 242 242 242 242 498), lower := (rows 97 14 37 265 16 32 64 128 256), losses := [] }

theorem u21148 : Upper (D 8) (R 8) [96,12,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21148 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21149 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 266 241 241 241 241 497), lower := (rows 97 14 37 266 16 32 64 128 256), losses := [] }

theorem u21149 : Upper (D 8) (R 8) [96,12,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21149 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21150 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 280 243 227 227 227 483), lower := (rows 97 14 37 280 16 32 64 128 256), losses := [] }

theorem u21150 : Upper (D 8) (R 8) [96,12,33,272] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21150 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21151 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 296 211 243 211 211 467), lower := (rows 97 14 37 296 16 32 64 128 256), losses := [] }

theorem u21151 : Upper (D 8) (R 8) [96,12,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21151 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21152 : PairBound 9 := { available := 179, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 328 179 179 243 179 435), lower := (rows 97 14 37 328 16 32 64 128 256), losses := [] }

theorem u21152 : Upper (D 8) (R 8) [96,12,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21152 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21153 : PairBound 9 := { available := 243, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 37 392 243 243 243 243 499), lower := (rows 97 14 37 392 16 32 64 128 256), losses := [] }

theorem u21153 : Upper (D 8) (R 8) [96,12,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21153 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21154 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 56 465 481 449 449 449), lower := (rows 97 14 38 56 16 32 64 128 256), losses := [] }

theorem u21154 : Upper (D 8) (R 8) [96,12,34,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21154 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21155 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 14, targets := 128 }], pairs := [(1,7)], upper := (rows 97 14 38 73 433 433 497 433 433), lower := (rows 97 14 38 73 16 32 64 128 256), losses := [] }

theorem u21155 : Upper (D 8) (R 8) [96,12,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21155 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21156 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 88 433 417 481 417 417), lower := (rows 97 14 38 88 16 32 64 128 256), losses := [] }

theorem u21156 : Upper (D 8) (R 8) [96,12,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21156 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21157 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 104 401 433 465 401 401), lower := (rows 97 14 38 104 16 32 64 128 256), losses := [] }

theorem u21157 : Upper (D 8) (R 8) [96,12,34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21157 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21158 : Route 9 := (fun mask => (mask,id))

def c21158 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21158 : Upper (D 8) (R 8) [96,12,34,129] 13 := by
  apply FastRouting.sound _ _ [96,12,34,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21158 c21158
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13811
  · exact u13812
  · exact u13813
  · exact u13814
  · exact u13815
  · exact u13816
  · exact u13817
  · exact u13818
  · exact u13819
  · exact u13820

def r21159 : Route 9 := (fun mask => (mask,id))

def c21159 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21159 : Upper (D 8) (R 8) [96,12,34,144] 13 := by
  apply FastRouting.sound _ _ [96,12,34,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21159 c21159
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13821
  · exact u13822
  · exact u13823
  · exact u13824
  · exact u13825
  · exact u13826
  · exact u13827
  · exact u13828
  · exact u13829
  · exact u13830

def b21160 : PairBound 9 := { available := 465, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 168 465 497 465 465 465), lower := (rows 97 14 38 168 16 32 64 128 256), losses := [] }

theorem u21160 : Upper (D 8) (R 8) [96,12,34,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21160 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21161 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 200 433 433 497 433 433), lower := (rows 97 14 38 200 16 32 64 128 256), losses := [] }

theorem u21161 : Upper (D 8) (R 8) [96,12,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21161 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21162 : Route 9 := (fun mask => (mask,id))

def c21162 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21162 : Upper (D 8) (R 8) [96,12,34,257] 13 := by
  apply FastRouting.sound _ _ [96,12,34,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21162 c21162
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13841
  · exact u13842
  · exact u13843
  · exact u13844
  · exact u13845
  · exact u13846

def r21163 : Route 9 := (fun mask => (mask,id))

def c21163 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21163 : Upper (D 8) (R 8) [96,12,34,272] 13 := by
  apply FastRouting.sound _ _ [96,12,34,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21163 c21163
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13847
  · exact u13848
  · exact u13849
  · exact u13850
  · exact u13851
  · exact u13852

def b21164 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 97 14 38 296 209 241 209 209 465), lower := (rows 97 14 38 296 16 32 64 128 256), losses := [] }

theorem u21164 : Upper (D 8) (R 8) [96,12,34,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21164 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21165 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 14 38 328 177 177 241 177 433), lower := (rows 97 14 38 328 16 32 64 128 256), losses := [] }

theorem u21165 : Upper (D 8) (R 8) [96,12,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21165 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21166 : Route 9 := (fun mask => (mask,id))

def c21166 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21166 : Upper (D 8) (R 8) [96,12,34,384] 13 := by
  apply FastRouting.sound _ _ [96,12,34,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21166 c21166
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13857
  · exact u13858
  · exact u13859
  · exact u13860
  · exact u13861
  · exact u13862

def b21167 : PairBound 9 := { available := 419, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 52 73 435 419 483 419 419), lower := (rows 97 14 52 73 16 32 64 128 256), losses := [] }

theorem u21167 : Upper (D 8) (R 8) [96,12,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21167 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21168 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 404, targets := 64 }], pairs := [(2,6)], upper := (rows 97 14 52 74 433 417 481 417 417), lower := (rows 97 14 52 74 16 32 64 128 256), losses := [] }

theorem u21168 : Upper (D 8) (R 8) [96,12,48,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21168 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21169 : PairBound 9 := { available := 387, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 97 14 52 104 403 419 451 387 387), lower := (rows 97 14 52 104 16 32 64 128 256), losses := [] }

theorem u21169 : Upper (D 8) (R 8) [96,12,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21169 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21170_3 : Upper (D 8) (R 8) [96,12,48,129,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12667

def r21170 : Route 9 := (fun mask => (mask,id))

def c21170 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21170 : Upper (D 8) (R 8) [96,12,48,129] 13 := by
  apply FastRouting.sound _ _ [96,12,48,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r21170 c21170
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21170_3
  · exact u13876
  · exact u13877
  · exact u13878
  · exact u13879
  · exact u13880
  · exact u13881
  · exact u13882
  · exact u13883
  · exact u13884
  · exact u13885
  · exact u13886
  · exact u13887
  · exact u13888
  · exact u13889

def r21171 : Route 9 := (fun mask => (mask,id))

def c21171 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21171 : Upper (D 8) (R 8) [96,12,48,130] 13 := by
  apply FastRouting.sound _ _ [96,12,48,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21171 c21171
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13890
  · exact u13891
  · exact u13892
  · exact u13893
  · exact u13894
  · exact u13895
  · exact u13896
  · exact u13897
  · exact u13898
  · exact u13899

theorem m21172_3 : Upper (D 8) (R 8) [96,12,48,160,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12668

def r21172 : Route 9 := (fun mask => (mask,id))

def c21172 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 6 => 2 | 10 => 3 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u21172 : Upper (D 8) (R 8) [96,12,48,160] 13 := by
  apply FastRouting.sound _ _ [96,12,48,160] 13 (by decide) (choices 2) [3,65,66,129,130,192,257,258,320,384] r21172 c21172
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21172_3
  · exact u13900
  · exact u13901
  · exact u13902
  · exact u13903
  · exact u13904
  · exact u13905
  · exact u13906
  · exact u13907
  · exact u13908

theorem m21173_3 : Upper (D 8) (R 8) [96,12,48,192,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12669

def r21173 : Route 9 := (fun mask => (mask,id))

def c21173 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21173 : Upper (D 8) (R 8) [96,12,48,192] 13 := by
  apply FastRouting.sound _ _ [96,12,48,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21173 c21173
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21173_3
  · exact u13909
  · exact u13910
  · exact u13911
  · exact u13912
  · exact u13913
  · exact u13914
  · exact u13915
  · exact u13916
  · exact u13917

theorem m21174_3 : Upper (D 8) (R 8) [96,12,48,257,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12670

def r21174 : Route 9 := (fun mask => (mask,id))

def c21174 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21174 : Upper (D 8) (R 8) [96,12,48,257] 13 := by
  apply FastRouting.sound _ _ [96,12,48,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21174 c21174
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21174_3
  · exact u13918
  · exact u13919
  · exact u13920
  · exact u13921
  · exact u13922
  · exact u13923
  · exact u13924
  · exact u13925
  · exact u13926

def r21175 : Route 9 := (fun mask => (mask,id))

def c21175 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21175 : Upper (D 8) (R 8) [96,12,48,258] 13 := by
  apply FastRouting.sound _ _ [96,12,48,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21175 c21175
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u13927
  · exact u13928
  · exact u13929
  · exact u13930
  · exact u13931
  · exact u13932

theorem m21176_3 : Upper (D 8) (R 8) [96,12,48,288,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12671

def r21176 : Route 9 := (fun mask => (mask,id))

def c21176 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21176 : Upper (D 8) (R 8) [96,12,48,288] 13 := by
  apply FastRouting.sound _ _ [96,12,48,288] 13 (by decide) (choices 2) [3,65,66,129,130,192] r21176 c21176
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21176_3
  · exact u13933
  · exact u13934
  · exact u13935
  · exact u13936
  · exact u13937

theorem m21177_3 : Upper (D 8) (R 8) [96,12,48,320,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12672

def r21177 : Route 9 := (fun mask => (mask,id))

def c21177 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21177 : Upper (D 8) (R 8) [96,12,48,320] 13 := by
  apply FastRouting.sound _ _ [96,12,48,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21177 c21177
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21177_3
  · exact u13938
  · exact u13939
  · exact u13940
  · exact u13941
  · exact u13942

theorem m21178_3 : Upper (D 8) (R 8) [96,12,48,384,3] 13 :=
  permutation_upper _ _ _ [96,5,24,34,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12673

def r21178 : Route 9 := (fun mask => (mask,id))

def c21178 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21178 : Upper (D 8) (R 8) [96,12,48,384] 13 := by
  apply FastRouting.sound _ _ [96,12,48,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21178 c21178
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21178_3
  · exact u13943
  · exact u13944
  · exact u13945
  · exact u13946
  · exact u13947
  · exact u13948
  · exact u13949
  · exact u13950
  · exact u13951

def b21179 : PairBound 9 := { available := 434, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 14 69 137 434 434 498 434 434), lower := (rows 97 14 69 137 16 32 64 128 256), losses := [] }

theorem u21179 : Upper (D 8) (R 8) [96,12,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21179 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u21179
end Delivery.IrregularNine14.P08
