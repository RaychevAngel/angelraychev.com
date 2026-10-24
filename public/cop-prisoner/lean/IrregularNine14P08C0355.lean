import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0208
import IrregularNine14P08C0209
import IrregularNine14P08C0210
import IrregularNine14P08C0211
import IrregularNine14P08C0212
import IrregularNine14P08C0213
import IrregularNine14P08C0214
import IrregularNine14P08C0215
import IrregularNine14P08C0216
import IrregularNine14P08C0217
import IrregularNine14P08C0218
import IrregularNine14P08C0219
import IrregularNine14P08C0221
import IrregularNine14P08C0222
import IrregularNine14P08C0223
import IrregularNine14P08C0224
import IrregularNine14P08C0225
import IrregularNine14P08C0226
import IrregularNine14P08C0227
import IrregularNine14P08C0228
import IrregularNine14P08C0229
import IrregularNine14P08C0230
import IrregularNine14P08C0231
import IrregularNine14P08C0232
import IrregularNine14P08C0233
import IrregularNine14P08C0234

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m21300_5 : Upper (D 8) (R 8) [96,17,136,258,5] 13 :=
  permutation_upper _ _ _ [96,5,9,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12539

theorem m21300_33 : Upper (D 8) (R 8) [96,17,136,258,33] 13 :=
  permutation_upper _ _ _ [96,5,33,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12751

theorem m21300_36 : Upper (D 8) (R 8) [96,17,136,258,36] 13 :=
  permutation_upper _ _ _ [96,5,40,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12891

theorem m21300_65 : Upper (D 8) (R 8) [96,17,136,258,65] 13 :=
  permutation_upper _ _ _ [96,5,65,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12968

theorem m21300_68 : Upper (D 8) (R 8) [96,17,136,258,68] 13 :=
  permutation_upper _ _ _ [96,5,72,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13029

theorem m21300_96 : Upper (D 8) (R 8) [96,17,136,258,96] 13 :=
  permutation_upper _ _ _ [96,5,96,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13088

theorem m21300_129 : Upper (D 8) (R 8) [96,17,136,258,129] 13 :=
  permutation_upper _ _ _ [96,5,129,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13132

theorem m21300_132 : Upper (D 8) (R 8) [96,17,136,258,132] 13 :=
  permutation_upper _ _ _ [96,5,136,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13275

theorem m21300_160 : Upper (D 8) (R 8) [96,17,136,258,160] 13 :=
  permutation_upper _ _ _ [96,5,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13409

theorem m21300_192 : Upper (D 8) (R 8) [96,17,136,258,192] 13 :=
  permutation_upper _ _ _ [96,5,192,144,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13454

def r21300 : Route 9 := (fun mask => (mask,id))

def c21300 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21300 : Upper (D 8) (R 8) [96,17,136,258] 13 := by
  apply FastRouting.sound _ _ [96,17,136,258] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r21300 c21300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21300_5
  · exact m21300_33
  · exact m21300_36
  · exact m21300_65
  · exact m21300_68
  · exact m21300_96
  · exact m21300_129
  · exact m21300_132
  · exact m21300_160
  · exact m21300_192

theorem m21301_3 : Upper (D 8) (R 8) [96,17,136,260,3] 13 :=
  permutation_upper _ _ _ [96,5,3,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12496

theorem m21301_33 : Upper (D 8) (R 8) [96,17,136,260,33] 13 :=
  permutation_upper _ _ _ [96,5,33,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12752

theorem m21301_34 : Upper (D 8) (R 8) [96,17,136,260,34] 13 :=
  permutation_upper _ _ _ [96,5,34,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12788

theorem m21301_65 : Upper (D 8) (R 8) [96,17,136,260,65] 13 :=
  permutation_upper _ _ _ [96,5,65,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12969

theorem m21301_66 : Upper (D 8) (R 8) [96,17,136,260,66] 13 :=
  permutation_upper _ _ _ [96,5,66,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12990

theorem m21301_96 : Upper (D 8) (R 8) [96,17,136,260,96] 13 :=
  permutation_upper _ _ _ [96,5,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13089

theorem m21301_129 : Upper (D 8) (R 8) [96,17,136,260,129] 13 :=
  permutation_upper _ _ _ [96,5,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13133

theorem m21301_130 : Upper (D 8) (R 8) [96,17,136,260,130] 13 :=
  permutation_upper _ _ _ [96,5,130,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13181

theorem m21301_160 : Upper (D 8) (R 8) [96,17,136,260,160] 13 :=
  permutation_upper _ _ _ [96,5,160,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13410

theorem m21301_192 : Upper (D 8) (R 8) [96,17,136,260,192] 13 :=
  permutation_upper _ _ _ [96,5,192,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13455

def r21301 : Route 9 := (fun mask => (mask,id))

def c21301 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21301 : Upper (D 8) (R 8) [96,17,136,260] 13 := by
  apply FastRouting.sound _ _ [96,17,136,260] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21301 c21301
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21301_3
  · exact m21301_33
  · exact m21301_34
  · exact m21301_65
  · exact m21301_66
  · exact m21301_96
  · exact m21301_129
  · exact m21301_130
  · exact m21301_160
  · exact m21301_192

theorem m21302_3 : Upper (D 8) (R 8) [96,17,136,288,3] 13 :=
  permutation_upper _ _ _ [96,5,3,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12497

theorem m21302_5 : Upper (D 8) (R 8) [96,17,136,288,5] 13 :=
  permutation_upper _ _ _ [96,5,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12540

theorem m21302_6 : Upper (D 8) (R 8) [96,17,136,288,6] 13 :=
  permutation_upper _ _ _ [96,5,10,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12619

theorem m21302_33 : Upper (D 8) (R 8) [96,17,136,288,33] 13 :=
  permutation_upper _ _ _ [96,5,33,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12753

theorem m21302_34 : Upper (D 8) (R 8) [96,17,136,288,34] 13 :=
  permutation_upper _ _ _ [96,5,34,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12789

theorem m21302_36 : Upper (D 8) (R 8) [96,17,136,288,36] 13 :=
  permutation_upper _ _ _ [96,5,40,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12892

theorem m21302_65 : Upper (D 8) (R 8) [96,17,136,288,65] 13 :=
  permutation_upper _ _ _ [96,5,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12970

theorem m21302_66 : Upper (D 8) (R 8) [96,17,136,288,66] 13 :=
  permutation_upper _ _ _ [96,5,66,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12991

theorem m21302_68 : Upper (D 8) (R 8) [96,17,136,288,68] 13 :=
  permutation_upper _ _ _ [96,5,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13030

theorem m21302_96 : Upper (D 8) (R 8) [96,17,136,288,96] 13 :=
  permutation_upper _ _ _ [96,5,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13090

theorem m21302_129 : Upper (D 8) (R 8) [96,17,136,288,129] 13 :=
  permutation_upper _ _ _ [96,5,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13134

theorem m21302_130 : Upper (D 8) (R 8) [96,17,136,288,130] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13182

theorem m21302_132 : Upper (D 8) (R 8) [96,17,136,288,132] 13 :=
  permutation_upper _ _ _ [96,5,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13276

theorem m21302_160 : Upper (D 8) (R 8) [96,17,136,288,160] 13 :=
  permutation_upper _ _ _ [96,5,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13411

theorem m21302_192 : Upper (D 8) (R 8) [96,17,136,288,192] 13 :=
  permutation_upper _ _ _ [96,5,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13456

def r21302 : Route 9 := (fun mask => (mask,id))

def c21302 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 257 => 8 | 10 => 3 | 258 => 8 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21302 : Upper (D 8) (R 8) [96,17,136,288] 13 := by
  apply FastRouting.sound _ _ [96,17,136,288] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r21302 c21302
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21302_3
  · exact m21302_5
  · exact m21302_6
  · exact m21302_33
  · exact m21302_34
  · exact m21302_36
  · exact m21302_65
  · exact m21302_66
  · exact m21302_68
  · exact m21302_96
  · exact m21302_129
  · exact m21302_130
  · exact m21302_132
  · exact m21302_160
  · exact m21302_192

theorem m21303_3 : Upper (D 8) (R 8) [96,17,136,320,3] 13 :=
  permutation_upper _ _ _ [96,5,3,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12498

theorem m21303_5 : Upper (D 8) (R 8) [96,17,136,320,5] 13 :=
  permutation_upper _ _ _ [96,5,9,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12541

theorem m21303_6 : Upper (D 8) (R 8) [96,17,136,320,6] 13 :=
  permutation_upper _ _ _ [96,5,10,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12620

theorem m21303_33 : Upper (D 8) (R 8) [96,17,136,320,33] 13 :=
  permutation_upper _ _ _ [96,5,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12754

theorem m21303_34 : Upper (D 8) (R 8) [96,17,136,320,34] 13 :=
  permutation_upper _ _ _ [96,5,34,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12790

theorem m21303_36 : Upper (D 8) (R 8) [96,17,136,320,36] 13 :=
  permutation_upper _ _ _ [96,5,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12893

theorem m21303_129 : Upper (D 8) (R 8) [96,17,136,320,129] 13 :=
  permutation_upper _ _ _ [96,5,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13135

theorem m21303_130 : Upper (D 8) (R 8) [96,17,136,320,130] 13 :=
  permutation_upper _ _ _ [96,5,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13183

theorem m21303_132 : Upper (D 8) (R 8) [96,17,136,320,132] 13 :=
  permutation_upper _ _ _ [96,5,136,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13277

theorem m21303_160 : Upper (D 8) (R 8) [96,17,136,320,160] 13 :=
  permutation_upper _ _ _ [96,5,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13412

def r21303 : Route 9 := (fun mask => (mask,id))

def c21303 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 65 => 6 | 257 => 8 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21303 : Upper (D 8) (R 8) [96,17,136,320] 13 := by
  apply FastRouting.sound _ _ [96,17,136,320] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r21303 c21303
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21303_3
  · exact m21303_5
  · exact m21303_6
  · exact m21303_33
  · exact m21303_34
  · exact m21303_36
  · exact m21303_129
  · exact m21303_130
  · exact m21303_132
  · exact m21303_160

theorem m21304_3 : Upper (D 8) (R 8) [96,17,160,192,3] 13 :=
  permutation_upper _ _ _ [96,5,3,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12499

theorem m21304_5 : Upper (D 8) (R 8) [96,17,160,192,5] 13 :=
  permutation_upper _ _ _ [96,5,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12545

theorem m21304_6 : Upper (D 8) (R 8) [96,17,160,192,6] 13 :=
  permutation_upper _ _ _ [96,5,10,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12627

theorem m21304_9 : Upper (D 8) (R 8) [96,17,160,192,9] 13 :=
  permutation_upper _ _ _ [96,5,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12552

theorem m21304_10 : Upper (D 8) (R 8) [96,17,160,192,10] 13 :=
  permutation_upper _ _ _ [96,5,10,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12633

theorem m21304_12 : Upper (D 8) (R 8) [96,17,160,192,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12703

theorem m21304_33 : Upper (D 8) (R 8) [96,17,160,192,33] 13 :=
  permutation_upper _ _ _ [96,5,33,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12755

theorem m21304_34 : Upper (D 8) (R 8) [96,17,160,192,34] 13 :=
  permutation_upper _ _ _ [96,5,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12791

theorem m21304_36 : Upper (D 8) (R 8) [96,17,160,192,36] 13 :=
  permutation_upper _ _ _ [96,5,40,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12898

theorem m21304_40 : Upper (D 8) (R 8) [96,17,160,192,40] 13 :=
  permutation_upper _ _ _ [96,5,40,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12906

theorem m21304_257 : Upper (D 8) (R 8) [96,17,160,192,257] 13 :=
  permutation_upper _ _ _ [96,5,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13479

theorem m21304_258 : Upper (D 8) (R 8) [96,17,160,192,258] 13 :=
  permutation_upper _ _ _ [96,5,258,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13507

theorem m21304_260 : Upper (D 8) (R 8) [96,17,160,192,260] 13 :=
  permutation_upper _ _ _ [96,5,264,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13575

theorem m21304_264 : Upper (D 8) (R 8) [96,17,160,192,264] 13 :=
  permutation_upper _ _ _ [96,5,264,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13579

theorem m21304_288 : Upper (D 8) (R 8) [96,17,160,192,288] 13 :=
  permutation_upper _ _ _ [96,5,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13629

def r21304 : Route 9 := (fun mask => (mask,id))

def c21304 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21304 : Upper (D 8) (R 8) [96,17,160,192] 13 := by
  apply FastRouting.sound _ _ [96,17,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r21304 c21304
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21304_3
  · exact m21304_5
  · exact m21304_6
  · exact m21304_9
  · exact m21304_10
  · exact m21304_12
  · exact m21304_33
  · exact m21304_34
  · exact m21304_36
  · exact m21304_40
  · exact m21304_257
  · exact m21304_258
  · exact m21304_260
  · exact m21304_264
  · exact m21304_288

theorem m21305_6 : Upper (D 8) (R 8) [96,17,160,257,6] 13 :=
  permutation_upper _ _ _ [96,5,10,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12628

theorem m21305_10 : Upper (D 8) (R 8) [96,17,160,257,10] 13 :=
  permutation_upper _ _ _ [96,5,10,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12637

theorem m21305_12 : Upper (D 8) (R 8) [96,17,160,257,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12704

theorem m21305_34 : Upper (D 8) (R 8) [96,17,160,257,34] 13 :=
  permutation_upper _ _ _ [96,5,34,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12792

theorem m21305_36 : Upper (D 8) (R 8) [96,17,160,257,36] 13 :=
  permutation_upper _ _ _ [96,5,40,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12899

theorem m21305_40 : Upper (D 8) (R 8) [96,17,160,257,40] 13 :=
  permutation_upper _ _ _ [96,5,40,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12914

theorem m21305_66 : Upper (D 8) (R 8) [96,17,160,257,66] 13 :=
  permutation_upper _ _ _ [96,5,66,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12992

theorem m21305_68 : Upper (D 8) (R 8) [96,17,160,257,68] 13 :=
  permutation_upper _ _ _ [96,5,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13034

theorem m21305_72 : Upper (D 8) (R 8) [96,17,160,257,72] 13 :=
  permutation_upper _ _ _ [96,5,72,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13040

theorem m21305_96 : Upper (D 8) (R 8) [96,17,160,257,96] 13 :=
  permutation_upper _ _ _ [96,5,96,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13091

theorem m21305_130 : Upper (D 8) (R 8) [96,17,160,257,130] 13 :=
  permutation_upper _ _ _ [96,5,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13184

theorem m21305_132 : Upper (D 8) (R 8) [96,17,160,257,132] 13 :=
  permutation_upper _ _ _ [96,5,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13280

theorem m21305_136 : Upper (D 8) (R 8) [96,17,160,257,136] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13291

theorem m21305_160 : Upper (D 8) (R 8) [96,17,160,257,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13413

theorem m21305_192 : Upper (D 8) (R 8) [96,17,160,257,192] 13 :=
  permutation_upper _ _ _ [96,5,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13457

def r21305 : Route 9 := (fun mask => (mask,id))

def c21305 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21305 : Upper (D 8) (R 8) [96,17,160,257] 13 := by
  apply FastRouting.sound _ _ [96,17,160,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,66,68,72,96,130,132,136,160,192] r21305 c21305
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21305_6
  · exact m21305_10
  · exact m21305_12
  · exact m21305_34
  · exact m21305_36
  · exact m21305_40
  · exact m21305_66
  · exact m21305_68
  · exact m21305_72
  · exact m21305_96
  · exact m21305_130
  · exact m21305_132
  · exact m21305_136
  · exact m21305_160
  · exact m21305_192

theorem m21306_5 : Upper (D 8) (R 8) [96,17,160,258,5] 13 :=
  permutation_upper _ _ _ [96,5,9,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12546

theorem m21306_9 : Upper (D 8) (R 8) [96,17,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,9,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12556

theorem m21306_12 : Upper (D 8) (R 8) [96,17,160,258,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12705

theorem m21306_33 : Upper (D 8) (R 8) [96,17,160,258,33] 13 :=
  permutation_upper _ _ _ [96,5,33,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12756

theorem m21306_36 : Upper (D 8) (R 8) [96,17,160,258,36] 13 :=
  permutation_upper _ _ _ [96,5,40,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12900

theorem m21306_40 : Upper (D 8) (R 8) [96,17,160,258,40] 13 :=
  permutation_upper _ _ _ [96,5,40,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12920

theorem m21306_65 : Upper (D 8) (R 8) [96,17,160,258,65] 13 :=
  permutation_upper _ _ _ [96,5,65,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12971

theorem m21306_68 : Upper (D 8) (R 8) [96,17,160,258,68] 13 :=
  permutation_upper _ _ _ [96,5,72,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13035

theorem m21306_72 : Upper (D 8) (R 8) [96,17,160,258,72] 13 :=
  permutation_upper _ _ _ [96,5,72,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13042

theorem m21306_96 : Upper (D 8) (R 8) [96,17,160,258,96] 13 :=
  permutation_upper _ _ _ [96,5,96,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13092

theorem m21306_129 : Upper (D 8) (R 8) [96,17,160,258,129] 13 :=
  permutation_upper _ _ _ [96,5,129,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13136

theorem m21306_132 : Upper (D 8) (R 8) [96,17,160,258,132] 13 :=
  permutation_upper _ _ _ [96,5,136,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13281

theorem m21306_136 : Upper (D 8) (R 8) [96,17,160,258,136] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13297

theorem m21306_160 : Upper (D 8) (R 8) [96,17,160,258,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13414

theorem m21306_192 : Upper (D 8) (R 8) [96,17,160,258,192] 13 :=
  permutation_upper _ _ _ [96,5,192,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13458

def r21306 : Route 9 := (fun mask => (mask,id))

def c21306 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21306 : Upper (D 8) (R 8) [96,17,160,258] 13 := by
  apply FastRouting.sound _ _ [96,17,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r21306 c21306
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21306_5
  · exact m21306_9
  · exact m21306_12
  · exact m21306_33
  · exact m21306_36
  · exact m21306_40
  · exact m21306_65
  · exact m21306_68
  · exact m21306_72
  · exact m21306_96
  · exact m21306_129
  · exact m21306_132
  · exact m21306_136
  · exact m21306_160
  · exact m21306_192

theorem m21307_3 : Upper (D 8) (R 8) [96,17,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,3,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12500

theorem m21307_9 : Upper (D 8) (R 8) [96,17,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,9,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12561

theorem m21307_10 : Upper (D 8) (R 8) [96,17,160,260,10] 13 :=
  permutation_upper _ _ _ [96,5,10,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12643

theorem m21307_33 : Upper (D 8) (R 8) [96,17,160,260,33] 13 :=
  permutation_upper _ _ _ [96,5,33,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12757

theorem m21307_34 : Upper (D 8) (R 8) [96,17,160,260,34] 13 :=
  permutation_upper _ _ _ [96,5,34,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12793

theorem m21307_40 : Upper (D 8) (R 8) [96,17,160,260,40] 13 :=
  permutation_upper _ _ _ [96,5,40,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12929

theorem m21307_65 : Upper (D 8) (R 8) [96,17,160,260,65] 13 :=
  permutation_upper _ _ _ [96,5,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12972

theorem m21307_66 : Upper (D 8) (R 8) [96,17,160,260,66] 13 :=
  permutation_upper _ _ _ [96,5,66,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12993

theorem m21307_72 : Upper (D 8) (R 8) [96,17,160,260,72] 13 :=
  permutation_upper _ _ _ [96,5,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13046

theorem m21307_96 : Upper (D 8) (R 8) [96,17,160,260,96] 13 :=
  permutation_upper _ _ _ [96,5,96,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13093

theorem m21307_129 : Upper (D 8) (R 8) [96,17,160,260,129] 13 :=
  permutation_upper _ _ _ [96,5,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13137

theorem m21307_130 : Upper (D 8) (R 8) [96,17,160,260,130] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13185

theorem m21307_136 : Upper (D 8) (R 8) [96,17,160,260,136] 13 :=
  permutation_upper _ _ _ [96,5,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13306

theorem m21307_160 : Upper (D 8) (R 8) [96,17,160,260,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13415

theorem m21307_192 : Upper (D 8) (R 8) [96,17,160,260,192] 13 :=
  permutation_upper _ _ _ [96,5,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13459

def r21307 : Route 9 := (fun mask => (mask,id))

def c21307 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21307 : Upper (D 8) (R 8) [96,17,160,260] 13 := by
  apply FastRouting.sound _ _ [96,17,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r21307 c21307
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21307_3
  · exact m21307_9
  · exact m21307_10
  · exact m21307_33
  · exact m21307_34
  · exact m21307_40
  · exact m21307_65
  · exact m21307_66
  · exact m21307_72
  · exact m21307_96
  · exact m21307_129
  · exact m21307_130
  · exact m21307_136
  · exact m21307_160
  · exact m21307_192

theorem m21308_3 : Upper (D 8) (R 8) [96,17,160,288,3] 13 :=
  permutation_upper _ _ _ [96,5,3,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12501

theorem m21308_5 : Upper (D 8) (R 8) [96,17,160,288,5] 13 :=
  permutation_upper _ _ _ [96,5,9,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12547

theorem m21308_6 : Upper (D 8) (R 8) [96,17,160,288,6] 13 :=
  permutation_upper _ _ _ [96,5,10,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12629

theorem m21308_9 : Upper (D 8) (R 8) [96,17,160,288,9] 13 :=
  permutation_upper _ _ _ [96,5,9,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12566

theorem m21308_10 : Upper (D 8) (R 8) [96,17,160,288,10] 13 :=
  permutation_upper _ _ _ [96,5,10,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12649

theorem m21308_12 : Upper (D 8) (R 8) [96,17,160,288,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12706

theorem m21308_65 : Upper (D 8) (R 8) [96,17,160,288,65] 13 :=
  permutation_upper _ _ _ [96,5,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12973

theorem m21308_66 : Upper (D 8) (R 8) [96,17,160,288,66] 13 :=
  permutation_upper _ _ _ [96,5,66,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12994

theorem m21308_68 : Upper (D 8) (R 8) [96,17,160,288,68] 13 :=
  permutation_upper _ _ _ [96,5,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13036

theorem m21308_72 : Upper (D 8) (R 8) [96,17,160,288,72] 13 :=
  permutation_upper _ _ _ [96,5,72,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13050

theorem m21308_129 : Upper (D 8) (R 8) [96,17,160,288,129] 13 :=
  permutation_upper _ _ _ [96,5,129,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13138

theorem m21308_130 : Upper (D 8) (R 8) [96,17,160,288,130] 13 :=
  permutation_upper _ _ _ [96,5,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13186

theorem m21308_132 : Upper (D 8) (R 8) [96,17,160,288,132] 13 :=
  permutation_upper _ _ _ [96,5,136,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13282

theorem m21308_136 : Upper (D 8) (R 8) [96,17,160,288,136] 13 :=
  permutation_upper _ _ _ [96,5,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13315

theorem m21308_192 : Upper (D 8) (R 8) [96,17,160,288,192] 13 :=
  permutation_upper _ _ _ [96,5,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13460

def r21308 : Route 9 := (fun mask => (mask,id))

def c21308 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 257 => 8 | 34 => 5 | 258 => 8 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21308 : Upper (D 8) (R 8) [96,17,160,288] 13 := by
  apply FastRouting.sound _ _ [96,17,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72,129,130,132,136,192] r21308 c21308
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21308_3
  · exact m21308_5
  · exact m21308_6
  · exact m21308_9
  · exact m21308_10
  · exact m21308_12
  · exact m21308_65
  · exact m21308_66
  · exact m21308_68
  · exact m21308_72
  · exact m21308_129
  · exact m21308_130
  · exact m21308_132
  · exact m21308_136
  · exact m21308_192

theorem m21309_3 : Upper (D 8) (R 8) [96,17,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,3,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12502

theorem m21309_5 : Upper (D 8) (R 8) [96,17,160,320,5] 13 :=
  permutation_upper _ _ _ [96,5,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12548

theorem m21309_6 : Upper (D 8) (R 8) [96,17,160,320,6] 13 :=
  permutation_upper _ _ _ [96,5,10,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12630

theorem m21309_9 : Upper (D 8) (R 8) [96,17,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12570

theorem m21309_10 : Upper (D 8) (R 8) [96,17,160,320,10] 13 :=
  permutation_upper _ _ _ [96,5,10,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12652

theorem m21309_12 : Upper (D 8) (R 8) [96,17,160,320,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12707

theorem m21309_33 : Upper (D 8) (R 8) [96,17,160,320,33] 13 :=
  permutation_upper _ _ _ [96,5,33,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12758

theorem m21309_34 : Upper (D 8) (R 8) [96,17,160,320,34] 13 :=
  permutation_upper _ _ _ [96,5,34,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12794

theorem m21309_36 : Upper (D 8) (R 8) [96,17,160,320,36] 13 :=
  permutation_upper _ _ _ [96,5,40,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12901

theorem m21309_40 : Upper (D 8) (R 8) [96,17,160,320,40] 13 :=
  permutation_upper _ _ _ [96,5,40,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12938

theorem m21309_129 : Upper (D 8) (R 8) [96,17,160,320,129] 13 :=
  permutation_upper _ _ _ [96,5,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13139

theorem m21309_130 : Upper (D 8) (R 8) [96,17,160,320,130] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13187

theorem m21309_132 : Upper (D 8) (R 8) [96,17,160,320,132] 13 :=
  permutation_upper _ _ _ [96,5,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13283

theorem m21309_136 : Upper (D 8) (R 8) [96,17,160,320,136] 13 :=
  permutation_upper _ _ _ [96,5,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13320

theorem m21309_160 : Upper (D 8) (R 8) [96,17,160,320,160] 13 :=
  permutation_upper _ _ _ [96,5,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13416

def r21309 : Route 9 := (fun mask => (mask,id))

def c21309 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21309 : Upper (D 8) (R 8) [96,17,160,320] 13 := by
  apply FastRouting.sound _ _ [96,17,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,129,130,132,136,160] r21309 c21309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21309_3
  · exact m21309_5
  · exact m21309_6
  · exact m21309_9
  · exact m21309_10
  · exact m21309_12
  · exact m21309_33
  · exact m21309_34
  · exact m21309_36
  · exact m21309_40
  · exact m21309_129
  · exact m21309_130
  · exact m21309_132
  · exact m21309_136
  · exact m21309_160

theorem m21310_3 : Upper (D 8) (R 8) [96,17,160,384,3] 13 :=
  permutation_upper _ _ _ [96,5,3,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12503

theorem m21310_5 : Upper (D 8) (R 8) [96,17,160,384,5] 13 :=
  permutation_upper _ _ _ [96,5,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12549

theorem m21310_6 : Upper (D 8) (R 8) [96,17,160,384,6] 13 :=
  permutation_upper _ _ _ [96,5,10,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12631

theorem m21310_9 : Upper (D 8) (R 8) [96,17,160,384,9] 13 :=
  permutation_upper _ _ _ [96,5,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12574

theorem m21310_10 : Upper (D 8) (R 8) [96,17,160,384,10] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12657

theorem m21310_12 : Upper (D 8) (R 8) [96,17,160,384,12] 13 :=
  permutation_upper _ _ _ [96,5,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12708

theorem m21310_33 : Upper (D 8) (R 8) [96,17,160,384,33] 13 :=
  permutation_upper _ _ _ [96,5,33,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12759

theorem m21310_34 : Upper (D 8) (R 8) [96,17,160,384,34] 13 :=
  permutation_upper _ _ _ [96,5,34,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12795

theorem m21310_36 : Upper (D 8) (R 8) [96,17,160,384,36] 13 :=
  permutation_upper _ _ _ [96,5,40,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12902

theorem m21310_40 : Upper (D 8) (R 8) [96,17,160,384,40] 13 :=
  permutation_upper _ _ _ [96,5,40,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12946

theorem m21310_65 : Upper (D 8) (R 8) [96,17,160,384,65] 13 :=
  permutation_upper _ _ _ [96,5,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12974

theorem m21310_66 : Upper (D 8) (R 8) [96,17,160,384,66] 13 :=
  permutation_upper _ _ _ [96,5,66,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12995

theorem m21310_68 : Upper (D 8) (R 8) [96,17,160,384,68] 13 :=
  permutation_upper _ _ _ [96,5,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13037

theorem m21310_72 : Upper (D 8) (R 8) [96,17,160,384,72] 13 :=
  permutation_upper _ _ _ [96,5,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13054

theorem m21310_96 : Upper (D 8) (R 8) [96,17,160,384,96] 13 :=
  permutation_upper _ _ _ [96,5,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13094

def r21310 : Route 9 := (fun mask => (mask,id))

def c21310 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21310 : Upper (D 8) (R 8) [96,17,160,384] 13 := by
  apply FastRouting.sound _ _ [96,17,160,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r21310 c21310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21310_3
  · exact m21310_5
  · exact m21310_6
  · exact m21310_9
  · exact m21310_10
  · exact m21310_12
  · exact m21310_33
  · exact m21310_34
  · exact m21310_36
  · exact m21310_40
  · exact m21310_65
  · exact m21310_66
  · exact m21310_68
  · exact m21310_72
  · exact m21310_96

theorem m21311_6 : Upper (D 8) (R 8) [96,17,192,257,6] 13 :=
  permutation_upper _ _ _ [96,5,10,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12634

theorem m21311_10 : Upper (D 8) (R 8) [96,17,192,257,10] 13 :=
  permutation_upper _ _ _ [96,5,10,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12638

theorem m21311_12 : Upper (D 8) (R 8) [96,17,192,257,12] 13 :=
  permutation_upper _ _ _ [96,5,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12709

theorem m21311_34 : Upper (D 8) (R 8) [96,17,192,257,34] 13 :=
  permutation_upper _ _ _ [96,5,34,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12796

theorem m21311_36 : Upper (D 8) (R 8) [96,17,192,257,36] 13 :=
  permutation_upper _ _ _ [96,5,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12907

theorem m21311_40 : Upper (D 8) (R 8) [96,17,192,257,40] 13 :=
  permutation_upper _ _ _ [96,5,40,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12915

theorem m21311_130 : Upper (D 8) (R 8) [96,17,192,257,130] 13 :=
  permutation_upper _ _ _ [96,5,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13188

theorem m21311_132 : Upper (D 8) (R 8) [96,17,192,257,132] 13 :=
  permutation_upper _ _ _ [96,5,136,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13285

theorem m21311_136 : Upper (D 8) (R 8) [96,17,192,257,136] 13 :=
  permutation_upper _ _ _ [96,5,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13292

theorem m21311_160 : Upper (D 8) (R 8) [96,17,192,257,160] 13 :=
  permutation_upper _ _ _ [96,5,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13417

def r21311 : Route 9 := (fun mask => (mask,id))

def c21311 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21311 : Upper (D 8) (R 8) [96,17,192,257] 13 := by
  apply FastRouting.sound _ _ [96,17,192,257] 13 (by decide) (choices 2) [6,10,12,34,36,40,130,132,136,160] r21311 c21311
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21311_6
  · exact m21311_10
  · exact m21311_12
  · exact m21311_34
  · exact m21311_36
  · exact m21311_40
  · exact m21311_130
  · exact m21311_132
  · exact m21311_136
  · exact m21311_160

theorem m21312_5 : Upper (D 8) (R 8) [96,17,192,258,5] 13 :=
  permutation_upper _ _ _ [96,5,9,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12553

theorem m21312_9 : Upper (D 8) (R 8) [96,17,192,258,9] 13 :=
  permutation_upper _ _ _ [96,5,9,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12557

theorem m21312_12 : Upper (D 8) (R 8) [96,17,192,258,12] 13 :=
  permutation_upper _ _ _ [96,5,24,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12710

theorem m21312_33 : Upper (D 8) (R 8) [96,17,192,258,33] 13 :=
  permutation_upper _ _ _ [96,5,33,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12760

theorem m21312_36 : Upper (D 8) (R 8) [96,17,192,258,36] 13 :=
  permutation_upper _ _ _ [96,5,40,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12908

theorem m21312_40 : Upper (D 8) (R 8) [96,17,192,258,40] 13 :=
  permutation_upper _ _ _ [96,5,40,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12921

theorem m21312_129 : Upper (D 8) (R 8) [96,17,192,258,129] 13 :=
  permutation_upper _ _ _ [96,5,129,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13140

theorem m21312_132 : Upper (D 8) (R 8) [96,17,192,258,132] 13 :=
  permutation_upper _ _ _ [96,5,136,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13286

theorem m21312_136 : Upper (D 8) (R 8) [96,17,192,258,136] 13 :=
  permutation_upper _ _ _ [96,5,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13298

theorem m21312_160 : Upper (D 8) (R 8) [96,17,192,258,160] 13 :=
  permutation_upper _ _ _ [96,5,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13418

def r21312 : Route 9 := (fun mask => (mask,id))

def c21312 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21312 : Upper (D 8) (R 8) [96,17,192,258] 13 := by
  apply FastRouting.sound _ _ [96,17,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r21312 c21312
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21312_5
  · exact m21312_9
  · exact m21312_12
  · exact m21312_33
  · exact m21312_36
  · exact m21312_40
  · exact m21312_129
  · exact m21312_132
  · exact m21312_136
  · exact m21312_160

theorem m21313_3 : Upper (D 8) (R 8) [96,17,192,260,3] 13 :=
  permutation_upper _ _ _ [96,5,3,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12504

theorem m21313_9 : Upper (D 8) (R 8) [96,17,192,260,9] 13 :=
  permutation_upper _ _ _ [96,5,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12562

theorem m21313_10 : Upper (D 8) (R 8) [96,17,192,260,10] 13 :=
  permutation_upper _ _ _ [96,5,10,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12644

theorem m21313_33 : Upper (D 8) (R 8) [96,17,192,260,33] 13 :=
  permutation_upper _ _ _ [96,5,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12761

theorem m21313_34 : Upper (D 8) (R 8) [96,17,192,260,34] 13 :=
  permutation_upper _ _ _ [96,5,34,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12797

theorem m21313_40 : Upper (D 8) (R 8) [96,17,192,260,40] 13 :=
  permutation_upper _ _ _ [96,5,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12930

theorem m21313_129 : Upper (D 8) (R 8) [96,17,192,260,129] 13 :=
  permutation_upper _ _ _ [96,5,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13141

theorem m21313_130 : Upper (D 8) (R 8) [96,17,192,260,130] 13 :=
  permutation_upper _ _ _ [96,5,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13189

theorem m21313_136 : Upper (D 8) (R 8) [96,17,192,260,136] 13 :=
  permutation_upper _ _ _ [96,5,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13307

theorem m21313_160 : Upper (D 8) (R 8) [96,17,192,260,160] 13 :=
  permutation_upper _ _ _ [96,5,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13419

def r21313 : Route 9 := (fun mask => (mask,id))

def c21313 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21313 : Upper (D 8) (R 8) [96,17,192,260] 13 := by
  apply FastRouting.sound _ _ [96,17,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21313 c21313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21313_3
  · exact m21313_9
  · exact m21313_10
  · exact m21313_33
  · exact m21313_34
  · exact m21313_40
  · exact m21313_129
  · exact m21313_130
  · exact m21313_136
  · exact m21313_160

theorem m21314_3 : Upper (D 8) (R 8) [96,17,192,288,3] 13 :=
  permutation_upper _ _ _ [96,5,3,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12505

theorem m21314_5 : Upper (D 8) (R 8) [96,17,192,288,5] 13 :=
  permutation_upper _ _ _ [96,5,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12554

theorem m21314_6 : Upper (D 8) (R 8) [96,17,192,288,6] 13 :=
  permutation_upper _ _ _ [96,5,10,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12635

theorem m21314_9 : Upper (D 8) (R 8) [96,17,192,288,9] 13 :=
  permutation_upper _ _ _ [96,5,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12567

theorem m21314_10 : Upper (D 8) (R 8) [96,17,192,288,10] 13 :=
  permutation_upper _ _ _ [96,5,10,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12650

theorem m21314_12 : Upper (D 8) (R 8) [96,17,192,288,12] 13 :=
  permutation_upper _ _ _ [96,5,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12711

theorem m21314_33 : Upper (D 8) (R 8) [96,17,192,288,33] 13 :=
  permutation_upper _ _ _ [96,5,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12762

theorem m21314_34 : Upper (D 8) (R 8) [96,17,192,288,34] 13 :=
  permutation_upper _ _ _ [96,5,34,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12798

theorem m21314_36 : Upper (D 8) (R 8) [96,17,192,288,36] 13 :=
  permutation_upper _ _ _ [96,5,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12909

theorem m21314_40 : Upper (D 8) (R 8) [96,17,192,288,40] 13 :=
  permutation_upper _ _ _ [96,5,40,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12934

theorem m21314_129 : Upper (D 8) (R 8) [96,17,192,288,129] 13 :=
  permutation_upper _ _ _ [96,5,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13142

theorem m21314_130 : Upper (D 8) (R 8) [96,17,192,288,130] 13 :=
  permutation_upper _ _ _ [96,5,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13190

theorem m21314_132 : Upper (D 8) (R 8) [96,17,192,288,132] 13 :=
  permutation_upper _ _ _ [96,5,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13287

theorem m21314_136 : Upper (D 8) (R 8) [96,17,192,288,136] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13316

theorem m21314_160 : Upper (D 8) (R 8) [96,17,192,288,160] 13 :=
  permutation_upper _ _ _ [96,5,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13420

def r21314 : Route 9 := (fun mask => (mask,id))

def c21314 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21314 : Upper (D 8) (R 8) [96,17,192,288] 13 := by
  apply FastRouting.sound _ _ [96,17,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,129,130,132,136,160] r21314 c21314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21314_3
  · exact m21314_5
  · exact m21314_6
  · exact m21314_9
  · exact m21314_10
  · exact m21314_12
  · exact m21314_33
  · exact m21314_34
  · exact m21314_36
  · exact m21314_40
  · exact m21314_129
  · exact m21314_130
  · exact m21314_132
  · exact m21314_136
  · exact m21314_160

theorem m21315_3 : Upper (D 8) (R 8) [96,17,192,384,3] 13 :=
  permutation_upper _ _ _ [96,5,3,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12506

theorem m21315_5 : Upper (D 8) (R 8) [96,17,192,384,5] 13 :=
  permutation_upper _ _ _ [96,5,9,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12555

theorem m21315_6 : Upper (D 8) (R 8) [96,17,192,384,6] 13 :=
  permutation_upper _ _ _ [96,5,10,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12636

theorem m21315_9 : Upper (D 8) (R 8) [96,17,192,384,9] 13 :=
  permutation_upper _ _ _ [96,5,9,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12575

theorem m21315_10 : Upper (D 8) (R 8) [96,17,192,384,10] 13 :=
  permutation_upper _ _ _ [96,5,10,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12658

theorem m21315_12 : Upper (D 8) (R 8) [96,17,192,384,12] 13 :=
  permutation_upper _ _ _ [96,5,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12712

theorem m21315_33 : Upper (D 8) (R 8) [96,17,192,384,33] 13 :=
  permutation_upper _ _ _ [96,5,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12763

theorem m21315_34 : Upper (D 8) (R 8) [96,17,192,384,34] 13 :=
  permutation_upper _ _ _ [96,5,34,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12799

theorem m21315_36 : Upper (D 8) (R 8) [96,17,192,384,36] 13 :=
  permutation_upper _ _ _ [96,5,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12910

theorem m21315_40 : Upper (D 8) (R 8) [96,17,192,384,40] 13 :=
  permutation_upper _ _ _ [96,5,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12947

def r21315 : Route 9 := (fun mask => (mask,id))

def c21315 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21315 : Upper (D 8) (R 8) [96,17,192,384] 13 := by
  apply FastRouting.sound _ _ [96,17,192,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21315 c21315
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21315_3
  · exact m21315_5
  · exact m21315_6
  · exact m21315_9
  · exact m21315_10
  · exact m21315_12
  · exact m21315_33
  · exact m21315_34
  · exact m21315_36
  · exact m21315_40

def b21316 : PairBound 9 := { available := 457, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 42 473 489 457 457 457), lower := (rows 97 22 37 42 16 32 64 128 256), losses := [] }

theorem u21316 : Upper (D 8) (R 8) [96,20,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21316 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21317 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 74 441 425 489 425 425), lower := (rows 97 22 37 74 16 32 64 128 256), losses := [] }

theorem u21317 : Upper (D 8) (R 8) [96,20,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21317 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21318 : PairBound 9 := { available := 490, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 137 506 490 490 490 490), lower := (rows 97 22 37 137 16 32 64 128 256), losses := [] }

theorem u21318 : Upper (D 8) (R 8) [96,20,33,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21318 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21319 : PairBound 9 := { available := 489, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 138 505 489 489 489 489), lower := (rows 97 22 37 138 16 32 64 128 256), losses := [] }

theorem u21319 : Upper (D 8) (R 8) [96,20,33,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21319 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21320 : PairBound 9 := { available := 459, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 168 475 491 459 459 459), lower := (rows 97 22 37 168 16 32 64 128 256), losses := [] }

theorem u21320 : Upper (D 8) (R 8) [96,20,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21320 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21321 : PairBound 9 := { available := 427, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 200 443 427 491 427 427), lower := (rows 97 22 37 200 16 32 64 128 256), losses := [] }

theorem u21321 : Upper (D 8) (R 8) [96,20,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21321 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21322 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 265 250 234 234 234 490), lower := (rows 97 22 37 265 16 32 64 128 256), losses := [] }

theorem u21322 : Upper (D 8) (R 8) [96,20,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21322 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21323 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 266 249 233 233 233 489), lower := (rows 97 22 37 266 16 32 64 128 256), losses := [] }

theorem u21323 : Upper (D 8) (R 8) [96,20,33,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21323 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21324 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 296 219 235 203 203 459), lower := (rows 97 22 37 296 16 32 64 128 256), losses := [] }

theorem u21324 : Upper (D 8) (R 8) [96,20,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21324 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21325 : PairBound 9 := { available := 171, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 328 187 171 235 171 427), lower := (rows 97 22 37 328 16 32 64 128 256), losses := [] }

theorem u21325 : Upper (D 8) (R 8) [96,20,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21325 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21326 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 4, targets := 64 }], pairs := [(2,6)], upper := (rows 97 22 37 392 251 235 235 235 491), lower := (rows 97 22 37 392 16 32 64 128 256), losses := [] }

theorem u21326 : Upper (D 8) (R 8) [96,20,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21326 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21327_9 : Upper (D 8) (R 8) [96,20,34,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13095

theorem m21327_33 : Upper (D 8) (R 8) [96,20,34,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13720

theorem m21327_40 : Upper (D 8) (R 8) [96,20,34,129,40] 13 :=
  permutation_upper _ _ _ [96,12,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13793

theorem m21327_65 : Upper (D 8) (R 8) [96,20,34,129,65] 13 :=
  permutation_upper _ _ _ [96,12,34,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13798

theorem m21327_72 : Upper (D 8) (R 8) [96,20,34,129,72] 13 :=
  permutation_upper _ _ _ [96,12,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13803

theorem m21327_96 : Upper (D 8) (R 8) [96,20,34,129,96] 13 :=
  permutation_upper _ _ _ [96,12,34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13808

theorem m21327_129 : Upper (D 8) (R 8) [96,20,34,129,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13814

theorem m21327_136 : Upper (D 8) (R 8) [96,20,34,129,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13824

theorem m21327_160 : Upper (D 8) (R 8) [96,20,34,129,160] 13 :=
  permutation_upper _ _ _ [96,12,34,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13831

theorem m21327_192 : Upper (D 8) (R 8) [96,20,34,129,192] 13 :=
  permutation_upper _ _ _ [96,12,34,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13836

theorem m21327_257 : Upper (D 8) (R 8) [96,20,34,129,257] 13 :=
  permutation_upper _ _ _ [96,12,34,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13844

theorem m21327_264 : Upper (D 8) (R 8) [96,20,34,129,264] 13 :=
  permutation_upper _ _ _ [96,12,34,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13850

theorem m21327_288 : Upper (D 8) (R 8) [96,20,34,129,288] 13 :=
  permutation_upper _ _ _ [96,12,34,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13853

theorem m21327_320 : Upper (D 8) (R 8) [96,20,34,129,320] 13 :=
  permutation_upper _ _ _ [96,12,34,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13855

theorem m21327_384 : Upper (D 8) (R 8) [96,20,34,129,384] 13 :=
  permutation_upper _ _ _ [96,12,34,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13860

def r21327 : Route 9 := (fun mask => (mask,id))

def c21327 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u21327 : Upper (D 8) (R 8) [96,20,34,129] 13 := by
  apply FastRouting.sound _ _ [96,20,34,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r21327 c21327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21327_9
  · exact m21327_33
  · exact m21327_40
  · exact m21327_65
  · exact m21327_72
  · exact m21327_96
  · exact m21327_129
  · exact m21327_136
  · exact m21327_160
  · exact m21327_192
  · exact m21327_257
  · exact m21327_264
  · exact m21327_288
  · exact m21327_320
  · exact m21327_384

theorem m21328_9 : Upper (D 8) (R 8) [96,20,34,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13331

theorem m21328_65 : Upper (D 8) (R 8) [96,20,34,160,65] 13 :=
  permutation_upper _ _ _ [96,12,34,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13799

theorem m21328_72 : Upper (D 8) (R 8) [96,20,34,160,72] 13 :=
  permutation_upper _ _ _ [96,12,34,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13804

theorem m21328_129 : Upper (D 8) (R 8) [96,20,34,160,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13815

theorem m21328_136 : Upper (D 8) (R 8) [96,20,34,160,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13825

theorem m21328_192 : Upper (D 8) (R 8) [96,20,34,160,192] 13 :=
  permutation_upper _ _ _ [96,12,34,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13837

theorem m21328_257 : Upper (D 8) (R 8) [96,20,34,160,257] 13 :=
  permutation_upper _ _ _ [96,12,34,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13845

theorem m21328_264 : Upper (D 8) (R 8) [96,20,34,160,264] 13 :=
  permutation_upper _ _ _ [96,12,34,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13851

theorem m21328_320 : Upper (D 8) (R 8) [96,20,34,160,320] 13 :=
  permutation_upper _ _ _ [96,12,34,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13856

theorem m21328_384 : Upper (D 8) (R 8) [96,20,34,160,384] 13 :=
  permutation_upper _ _ _ [96,12,34,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13861

def r21328 : Route 9 := (fun mask => (mask,id))

def c21328 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u21328 : Upper (D 8) (R 8) [96,20,34,160] 13 := by
  apply FastRouting.sound _ _ [96,20,34,160] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r21328 c21328
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21328_9
  · exact m21328_65
  · exact m21328_72
  · exact m21328_129
  · exact m21328_136
  · exact m21328_192
  · exact m21328_257
  · exact m21328_264
  · exact m21328_320
  · exact m21328_384

theorem m21329_9 : Upper (D 8) (R 8) [96,20,34,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13425

theorem m21329_33 : Upper (D 8) (R 8) [96,20,34,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13721

theorem m21329_40 : Upper (D 8) (R 8) [96,20,34,192,40] 13 :=
  permutation_upper _ _ _ [96,12,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13794

theorem m21329_129 : Upper (D 8) (R 8) [96,20,34,192,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13816

theorem m21329_136 : Upper (D 8) (R 8) [96,20,34,192,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13826

theorem m21329_160 : Upper (D 8) (R 8) [96,20,34,192,160] 13 :=
  permutation_upper _ _ _ [96,12,34,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13832

theorem m21329_257 : Upper (D 8) (R 8) [96,20,34,192,257] 13 :=
  permutation_upper _ _ _ [96,12,34,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13846

theorem m21329_264 : Upper (D 8) (R 8) [96,20,34,192,264] 13 :=
  permutation_upper _ _ _ [96,12,34,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13852

theorem m21329_288 : Upper (D 8) (R 8) [96,20,34,192,288] 13 :=
  permutation_upper _ _ _ [96,12,34,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13854

theorem m21329_384 : Upper (D 8) (R 8) [96,20,34,192,384] 13 :=
  permutation_upper _ _ _ [96,12,34,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13862

def r21329 : Route 9 := (fun mask => (mask,id))

def c21329 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21329 : Upper (D 8) (R 8) [96,20,34,192] 13 := by
  apply FastRouting.sound _ _ [96,20,34,192] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r21329 c21329
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21329_9
  · exact m21329_33
  · exact m21329_40
  · exact m21329_129
  · exact m21329_136
  · exact m21329_160
  · exact m21329_257
  · exact m21329_264
  · exact m21329_288
  · exact m21329_384

theorem m21330_9 : Upper (D 8) (R 8) [96,20,34,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13461

theorem m21330_33 : Upper (D 8) (R 8) [96,20,34,257,33] 13 :=
  permutation_upper _ _ _ [96,12,33,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13722

theorem m21330_40 : Upper (D 8) (R 8) [96,20,34,257,40] 13 :=
  permutation_upper _ _ _ [96,12,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13795

theorem m21330_65 : Upper (D 8) (R 8) [96,20,34,257,65] 13 :=
  permutation_upper _ _ _ [96,12,34,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13800

theorem m21330_72 : Upper (D 8) (R 8) [96,20,34,257,72] 13 :=
  permutation_upper _ _ _ [96,12,34,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13805

theorem m21330_96 : Upper (D 8) (R 8) [96,20,34,257,96] 13 :=
  permutation_upper _ _ _ [96,12,34,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13809

theorem m21330_129 : Upper (D 8) (R 8) [96,20,34,257,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13817

theorem m21330_136 : Upper (D 8) (R 8) [96,20,34,257,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13827

theorem m21330_160 : Upper (D 8) (R 8) [96,20,34,257,160] 13 :=
  permutation_upper _ _ _ [96,12,34,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13833

theorem m21330_192 : Upper (D 8) (R 8) [96,20,34,257,192] 13 :=
  permutation_upper _ _ _ [96,12,34,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13838

def r21330 : Route 9 := (fun mask => (mask,id))

def c21330 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21330 : Upper (D 8) (R 8) [96,20,34,257] 13 := by
  apply FastRouting.sound _ _ [96,20,34,257] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21330 c21330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21330_9
  · exact m21330_33
  · exact m21330_40
  · exact m21330_65
  · exact m21330_72
  · exact m21330_96
  · exact m21330_129
  · exact m21330_136
  · exact m21330_160
  · exact m21330_192

theorem m21331_9 : Upper (D 8) (R 8) [96,20,34,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13581

theorem m21331_65 : Upper (D 8) (R 8) [96,20,34,288,65] 13 :=
  permutation_upper _ _ _ [96,12,34,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13801

theorem m21331_72 : Upper (D 8) (R 8) [96,20,34,288,72] 13 :=
  permutation_upper _ _ _ [96,12,34,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13806

theorem m21331_129 : Upper (D 8) (R 8) [96,20,34,288,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13818

theorem m21331_136 : Upper (D 8) (R 8) [96,20,34,288,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13828

theorem m21331_192 : Upper (D 8) (R 8) [96,20,34,288,192] 13 :=
  permutation_upper _ _ _ [96,12,34,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13839

def r21331 : Route 9 := (fun mask => (mask,id))

def c21331 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21331 : Upper (D 8) (R 8) [96,20,34,288] 13 := by
  apply FastRouting.sound _ _ [96,20,34,288] 13 (by decide) (choices 2) [9,65,72,129,136,192] r21331 c21331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21331_9
  · exact m21331_65
  · exact m21331_72
  · exact m21331_129
  · exact m21331_136
  · exact m21331_192

theorem m21332_9 : Upper (D 8) (R 8) [96,20,34,320,9] 13 :=
  permutation_upper _ _ _ [96,5,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13630

theorem m21332_33 : Upper (D 8) (R 8) [96,20,34,320,33] 13 :=
  permutation_upper _ _ _ [96,12,33,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13723

theorem m21332_40 : Upper (D 8) (R 8) [96,20,34,320,40] 13 :=
  permutation_upper _ _ _ [96,12,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13796

theorem m21332_129 : Upper (D 8) (R 8) [96,20,34,320,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13819

theorem m21332_136 : Upper (D 8) (R 8) [96,20,34,320,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13829

theorem m21332_160 : Upper (D 8) (R 8) [96,20,34,320,160] 13 :=
  permutation_upper _ _ _ [96,12,34,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13834

def r21332 : Route 9 := (fun mask => (mask,id))

def c21332 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21332 : Upper (D 8) (R 8) [96,20,34,320] 13 := by
  apply FastRouting.sound _ _ [96,20,34,320] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21332 c21332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21332_9
  · exact m21332_33
  · exact m21332_40
  · exact m21332_129
  · exact m21332_136
  · exact m21332_160

theorem m21333_9 : Upper (D 8) (R 8) [96,20,34,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,18,40] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13644

theorem m21333_33 : Upper (D 8) (R 8) [96,20,34,384,33] 13 :=
  permutation_upper _ _ _ [96,12,33,34,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13724

theorem m21333_40 : Upper (D 8) (R 8) [96,20,34,384,40] 13 :=
  permutation_upper _ _ _ [96,12,34,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13797

theorem m21333_65 : Upper (D 8) (R 8) [96,20,34,384,65] 13 :=
  permutation_upper _ _ _ [96,12,34,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13802

theorem m21333_72 : Upper (D 8) (R 8) [96,20,34,384,72] 13 :=
  permutation_upper _ _ _ [96,12,34,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13807

theorem m21333_96 : Upper (D 8) (R 8) [96,20,34,384,96] 13 :=
  permutation_upper _ _ _ [96,12,34,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13810

theorem m21333_129 : Upper (D 8) (R 8) [96,20,34,384,129] 13 :=
  permutation_upper _ _ _ [96,12,34,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13820

theorem m21333_136 : Upper (D 8) (R 8) [96,20,34,384,136] 13 :=
  permutation_upper _ _ _ [96,12,34,144,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13830

theorem m21333_160 : Upper (D 8) (R 8) [96,20,34,384,160] 13 :=
  permutation_upper _ _ _ [96,12,34,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13835

theorem m21333_192 : Upper (D 8) (R 8) [96,20,34,384,192] 13 :=
  permutation_upper _ _ _ [96,12,34,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13840

def r21333 : Route 9 := (fun mask => (mask,id))

def c21333 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21333 : Upper (D 8) (R 8) [96,20,34,384] 13 := by
  apply FastRouting.sound _ _ [96,20,34,384] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21333 c21333
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21333_9
  · exact m21333_33
  · exact m21333_40
  · exact m21333_65
  · exact m21333_72
  · exact m21333_96
  · exact m21333_129
  · exact m21333_136
  · exact m21333_160
  · exact m21333_192

def b21334 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 22 44 42 465 481 449 449 449), lower := (rows 97 22 44 42 16 32 64 128 256), losses := [] }

theorem u21334 : Upper (D 8) (R 8) [96,20,40,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21334 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21335 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 22 44 74 433 417 481 417 417), lower := (rows 97 22 44 74 16 32 64 128 256), losses := [] }

theorem u21335 : Upper (D 8) (R 8) [96,20,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21335 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21336_3 : Upper (D 8) (R 8) [96,20,40,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,48,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12589

theorem m21336_33 : Upper (D 8) (R 8) [96,20,40,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13725

theorem m21336_34 : Upper (D 8) (R 8) [96,20,40,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13793

theorem m21336_65 : Upper (D 8) (R 8) [96,20,40,129,65] 13 :=
  permutation_upper _ _ _ [96,12,48,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13863

theorem m21336_66 : Upper (D 8) (R 8) [96,20,40,129,66] 13 :=
  permutation_upper _ _ _ [96,12,48,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13868

theorem m21336_96 : Upper (D 8) (R 8) [96,20,40,129,96] 13 :=
  permutation_upper _ _ _ [96,12,48,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13871

theorem m21336_129 : Upper (D 8) (R 8) [96,20,40,129,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13881

theorem m21336_130 : Upper (D 8) (R 8) [96,20,40,129,130] 13 :=
  permutation_upper _ _ _ [96,12,48,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13893

theorem m21336_160 : Upper (D 8) (R 8) [96,20,40,129,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13902

theorem m21336_192 : Upper (D 8) (R 8) [96,20,40,129,192] 13 :=
  permutation_upper _ _ _ [96,12,48,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13911

theorem m21336_257 : Upper (D 8) (R 8) [96,20,40,129,257] 13 :=
  permutation_upper _ _ _ [96,12,48,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13923

theorem m21336_258 : Upper (D 8) (R 8) [96,20,40,129,258] 13 :=
  permutation_upper _ _ _ [96,12,48,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13930

theorem m21336_288 : Upper (D 8) (R 8) [96,20,40,129,288] 13 :=
  permutation_upper _ _ _ [96,12,48,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13935

theorem m21336_320 : Upper (D 8) (R 8) [96,20,40,129,320] 13 :=
  permutation_upper _ _ _ [96,12,48,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13940

theorem m21336_384 : Upper (D 8) (R 8) [96,20,40,129,384] 13 :=
  permutation_upper _ _ _ [96,12,48,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13948

def r21336 : Route 9 := (fun mask => (mask,id))

def c21336 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21336 : Upper (D 8) (R 8) [96,20,40,129] 13 := by
  apply FastRouting.sound _ _ [96,20,40,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r21336 c21336
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21336_3
  · exact m21336_33
  · exact m21336_34
  · exact m21336_65
  · exact m21336_66
  · exact m21336_96
  · exact m21336_129
  · exact m21336_130
  · exact m21336_160
  · exact m21336_192
  · exact m21336_257
  · exact m21336_258
  · exact m21336_288
  · exact m21336_320
  · exact m21336_384

theorem m21337_33 : Upper (D 8) (R 8) [96,20,40,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13726

theorem m21337_65 : Upper (D 8) (R 8) [96,20,40,130,65] 13 :=
  permutation_upper _ _ _ [96,12,48,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13864

theorem m21337_96 : Upper (D 8) (R 8) [96,20,40,130,96] 13 :=
  permutation_upper _ _ _ [96,12,48,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13872

theorem m21337_129 : Upper (D 8) (R 8) [96,20,40,130,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13882

theorem m21337_160 : Upper (D 8) (R 8) [96,20,40,130,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13903

theorem m21337_192 : Upper (D 8) (R 8) [96,20,40,130,192] 13 :=
  permutation_upper _ _ _ [96,12,48,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13912

theorem m21337_257 : Upper (D 8) (R 8) [96,20,40,130,257] 13 :=
  permutation_upper _ _ _ [96,12,48,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13924

theorem m21337_288 : Upper (D 8) (R 8) [96,20,40,130,288] 13 :=
  permutation_upper _ _ _ [96,12,48,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13936

theorem m21337_320 : Upper (D 8) (R 8) [96,20,40,130,320] 13 :=
  permutation_upper _ _ _ [96,12,48,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13941

theorem m21337_384 : Upper (D 8) (R 8) [96,20,40,130,384] 13 :=
  permutation_upper _ _ _ [96,12,48,384,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13949

def r21337 : Route 9 := (fun mask => (mask,id))

def c21337 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21337 : Upper (D 8) (R 8) [96,20,40,130] 13 := by
  apply FastRouting.sound _ _ [96,20,40,130] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r21337 c21337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21337_33
  · exact m21337_65
  · exact m21337_96
  · exact m21337_129
  · exact m21337_160
  · exact m21337_192
  · exact m21337_257
  · exact m21337_288
  · exact m21337_320
  · exact m21337_384

def b21338 : PairBound 9 := { available := 451, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 22 44 168 467 483 451 451 451), lower := (rows 97 22 44 168 16 32 64 128 256), losses := [] }

theorem u21338 : Upper (D 8) (R 8) [96,20,40,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21338 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21339_3 : Upper (D 8) (R 8) [96,20,40,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12591

theorem m21339_33 : Upper (D 8) (R 8) [96,20,40,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13727

theorem m21339_34 : Upper (D 8) (R 8) [96,20,40,192,34] 13 :=
  permutation_upper _ _ _ [96,12,34,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13794

theorem m21339_129 : Upper (D 8) (R 8) [96,20,40,192,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13884

theorem m21339_130 : Upper (D 8) (R 8) [96,20,40,192,130] 13 :=
  permutation_upper _ _ _ [96,12,48,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13895

theorem m21339_160 : Upper (D 8) (R 8) [96,20,40,192,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13904

theorem m21339_257 : Upper (D 8) (R 8) [96,20,40,192,257] 13 :=
  permutation_upper _ _ _ [96,12,48,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13926

theorem m21339_258 : Upper (D 8) (R 8) [96,20,40,192,258] 13 :=
  permutation_upper _ _ _ [96,12,48,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13932

theorem m21339_288 : Upper (D 8) (R 8) [96,20,40,192,288] 13 :=
  permutation_upper _ _ _ [96,12,48,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13937

theorem m21339_384 : Upper (D 8) (R 8) [96,20,40,192,384] 13 :=
  permutation_upper _ _ _ [96,12,48,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13951

def r21339 : Route 9 := (fun mask => (mask,id))

def c21339 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21339 : Upper (D 8) (R 8) [96,20,40,192] 13 := by
  apply FastRouting.sound _ _ [96,20,40,192] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21339 c21339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21339_3
  · exact m21339_33
  · exact m21339_34
  · exact m21339_129
  · exact m21339_130
  · exact m21339_160
  · exact m21339_257
  · exact m21339_258
  · exact m21339_288
  · exact m21339_384

theorem m21340_3 : Upper (D 8) (R 8) [96,20,40,257,3] 13 :=
  permutation_upper _ _ _ [96,5,10,48,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12592

theorem m21340_33 : Upper (D 8) (R 8) [96,20,40,257,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13728

theorem m21340_34 : Upper (D 8) (R 8) [96,20,40,257,34] 13 :=
  permutation_upper _ _ _ [96,12,34,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13795

theorem m21340_65 : Upper (D 8) (R 8) [96,20,40,257,65] 13 :=
  permutation_upper _ _ _ [96,12,48,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13865

theorem m21340_66 : Upper (D 8) (R 8) [96,20,40,257,66] 13 :=
  permutation_upper _ _ _ [96,12,48,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13869

theorem m21340_96 : Upper (D 8) (R 8) [96,20,40,257,96] 13 :=
  permutation_upper _ _ _ [96,12,48,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13873

theorem m21340_129 : Upper (D 8) (R 8) [96,20,40,257,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13885

theorem m21340_130 : Upper (D 8) (R 8) [96,20,40,257,130] 13 :=
  permutation_upper _ _ _ [96,12,48,130,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13896

theorem m21340_160 : Upper (D 8) (R 8) [96,20,40,257,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13905

theorem m21340_192 : Upper (D 8) (R 8) [96,20,40,257,192] 13 :=
  permutation_upper _ _ _ [96,12,48,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13914

def r21340 : Route 9 := (fun mask => (mask,id))

def c21340 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21340 : Upper (D 8) (R 8) [96,20,40,257] 13 := by
  apply FastRouting.sound _ _ [96,20,40,257] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21340 c21340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21340_3
  · exact m21340_33
  · exact m21340_34
  · exact m21340_65
  · exact m21340_66
  · exact m21340_96
  · exact m21340_129
  · exact m21340_130
  · exact m21340_160
  · exact m21340_192

theorem m21341_33 : Upper (D 8) (R 8) [96,20,40,258,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13729

theorem m21341_65 : Upper (D 8) (R 8) [96,20,40,258,65] 13 :=
  permutation_upper _ _ _ [96,12,48,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13866

theorem m21341_96 : Upper (D 8) (R 8) [96,20,40,258,96] 13 :=
  permutation_upper _ _ _ [96,12,48,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13874

theorem m21341_129 : Upper (D 8) (R 8) [96,20,40,258,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13886

theorem m21341_160 : Upper (D 8) (R 8) [96,20,40,258,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13906

theorem m21341_192 : Upper (D 8) (R 8) [96,20,40,258,192] 13 :=
  permutation_upper _ _ _ [96,12,48,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13915

def r21341 : Route 9 := (fun mask => (mask,id))

def c21341 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21341 : Upper (D 8) (R 8) [96,20,40,258] 13 := by
  apply FastRouting.sound _ _ [96,20,40,258] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21341 c21341
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21341_33
  · exact m21341_65
  · exact m21341_96
  · exact m21341_129
  · exact m21341_160
  · exact m21341_192

def b21342 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 22 44 296 211 227 195 195 451), lower := (rows 97 22 44 296 16 32 64 128 256), losses := [] }

theorem u21342 : Upper (D 8) (R 8) [96,20,40,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21342 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21343_3 : Upper (D 8) (R 8) [96,20,40,320,3] 13 :=
  permutation_upper _ _ _ [96,5,10,48,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12594

theorem m21343_33 : Upper (D 8) (R 8) [96,20,40,320,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13730

theorem m21343_34 : Upper (D 8) (R 8) [96,20,40,320,34] 13 :=
  permutation_upper _ _ _ [96,12,34,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13796

theorem m21343_129 : Upper (D 8) (R 8) [96,20,40,320,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13888

theorem m21343_130 : Upper (D 8) (R 8) [96,20,40,320,130] 13 :=
  permutation_upper _ _ _ [96,12,48,130,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13898

theorem m21343_160 : Upper (D 8) (R 8) [96,20,40,320,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13907

def r21343 : Route 9 := (fun mask => (mask,id))

def c21343 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21343 : Upper (D 8) (R 8) [96,20,40,320] 13 := by
  apply FastRouting.sound _ _ [96,20,40,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21343 c21343
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21343_3
  · exact m21343_33
  · exact m21343_34
  · exact m21343_129
  · exact m21343_130
  · exact m21343_160

theorem m21344_3 : Upper (D 8) (R 8) [96,20,40,384,3] 13 :=
  permutation_upper _ _ _ [96,5,10,48,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12595

theorem m21344_33 : Upper (D 8) (R 8) [96,20,40,384,33] 13 :=
  permutation_upper _ _ _ [96,12,33,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13731

theorem m21344_34 : Upper (D 8) (R 8) [96,20,40,384,34] 13 :=
  permutation_upper _ _ _ [96,12,34,48,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13797

theorem m21344_65 : Upper (D 8) (R 8) [96,20,40,384,65] 13 :=
  permutation_upper _ _ _ [96,12,48,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13867

theorem m21344_66 : Upper (D 8) (R 8) [96,20,40,384,66] 13 :=
  permutation_upper _ _ _ [96,12,48,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13870

theorem m21344_96 : Upper (D 8) (R 8) [96,20,40,384,96] 13 :=
  permutation_upper _ _ _ [96,12,48,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13875

theorem m21344_129 : Upper (D 8) (R 8) [96,20,40,384,129] 13 :=
  permutation_upper _ _ _ [96,12,48,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13889

theorem m21344_130 : Upper (D 8) (R 8) [96,20,40,384,130] 13 :=
  permutation_upper _ _ _ [96,12,48,130,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13899

theorem m21344_160 : Upper (D 8) (R 8) [96,20,40,384,160] 13 :=
  permutation_upper _ _ _ [96,12,48,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13908

theorem m21344_192 : Upper (D 8) (R 8) [96,20,40,384,192] 13 :=
  permutation_upper _ _ _ [96,12,48,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13917

def r21344 : Route 9 := (fun mask => (mask,id))

def c21344 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21344 : Upper (D 8) (R 8) [96,20,40,384] 13 := by
  apply FastRouting.sound _ _ [96,20,40,384] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21344 c21344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21344_3
  · exact m21344_33
  · exact m21344_34
  · exact m21344_65
  · exact m21344_66
  · exact m21344_96
  · exact m21344_129
  · exact m21344_130
  · exact m21344_160
  · exact m21344_192

def b21345 : PairBound 9 := { available := 425, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 42 441 425 489 425 425), lower := (rows 97 22 69 42 16 32 64 128 256), losses := [] }

theorem u21345 : Upper (D 8) (R 8) [96,20,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21345 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21346 : PairBound 9 := { available := 426, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 137 442 426 490 426 426), lower := (rows 97 22 69 137 16 32 64 128 256), losses := [] }

theorem u21346 : Upper (D 8) (R 8) [96,20,65,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21346 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21347 : PairBound 9 := { available := 425, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 138 441 425 489 425 425), lower := (rows 97 22 69 138 16 32 64 128 256), losses := [] }

theorem u21347 : Upper (D 8) (R 8) [96,20,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21347 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21348 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 168 443 427 491 427 427), lower := (rows 97 22 69 168 16 32 64 128 256), losses := [] }

theorem u21348 : Upper (D 8) (R 8) [96,20,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21348 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21349 : PairBound 9 := { available := 170, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 265 186 170 234 170 426), lower := (rows 97 22 69 265 16 32 64 128 256), losses := [] }

theorem u21349 : Upper (D 8) (R 8) [96,20,65,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21349 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21350 : PairBound 9 := { available := 169, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 266 185 169 233 169 425), lower := (rows 97 22 69 266 16 32 64 128 256), losses := [] }

theorem u21350 : Upper (D 8) (R 8) [96,20,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21350 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21351 : PairBound 9 := { available := 171, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 296 187 171 235 171 427), lower := (rows 97 22 69 296 16 32 64 128 256), losses := [] }

theorem u21351 : Upper (D 8) (R 8) [96,20,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21351 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21352 : PairBound 9 := { available := 171, camps := [{ cop := 2, region := 442, targets := 64 }], pairs := [(1,6)], upper := (rows 97 22 69 392 187 171 235 171 427), lower := (rows 97 22 69 392 16 32 64 128 256), losses := [] }

theorem u21352 : Upper (D 8) (R 8) [96,20,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21352 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21353 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 22 70 137 441 425 489 425 425), lower := (rows 97 22 70 137 16 32 64 128 256), losses := [] }

theorem u21353 : Upper (D 8) (R 8) [96,20,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21353 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21354 : PairBound 9 := { available := 425, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 22 70 168 441 425 489 425 425), lower := (rows 97 22 70 168 16 32 64 128 256), losses := [] }

theorem u21354 : Upper (D 8) (R 8) [96,20,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21354 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21355 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 22 70 265 185 169 233 169 425), lower := (rows 97 22 70 265 16 32 64 128 256), losses := [] }

theorem u21355 : Upper (D 8) (R 8) [96,20,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21355 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21356 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 22 70 296 185 169 233 169 425), lower := (rows 97 22 70 296 16 32 64 128 256), losses := [] }

theorem u21356 : Upper (D 8) (R 8) [96,20,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21356 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21357 : PairBound 9 := { available := 169, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 97 22 70 392 185 169 233 169 425), lower := (rows 97 22 70 392 16 32 64 128 256), losses := [] }

theorem u21357 : Upper (D 8) (R 8) [96,20,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21357 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21358 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 97 22 76 42 433 417 481 417 417), lower := (rows 97 22 76 42 16 32 64 128 256), losses := [] }

theorem u21358 : Upper (D 8) (R 8) [96,20,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21358 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21359_3 : Upper (D 8) (R 8) [96,20,72,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12599

theorem m21359_33 : Upper (D 8) (R 8) [96,20,72,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13732

theorem m21359_34 : Upper (D 8) (R 8) [96,20,72,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13803

theorem m21359_129 : Upper (D 8) (R 8) [96,20,72,129,129] 13 :=
  permutation_upper _ _ _ [96,12,80,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14005

theorem m21359_130 : Upper (D 8) (R 8) [96,20,72,129,130] 13 :=
  permutation_upper _ _ _ [96,12,80,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14012

theorem m21359_160 : Upper (D 8) (R 8) [96,20,72,129,160] 13 :=
  permutation_upper _ _ _ [96,12,80,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14019

theorem m21359_257 : Upper (D 8) (R 8) [96,20,72,129,257] 13 :=
  permutation_upper _ _ _ [96,12,80,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14028

theorem m21359_258 : Upper (D 8) (R 8) [96,20,72,129,258] 13 :=
  permutation_upper _ _ _ [96,12,80,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14031

theorem m21359_288 : Upper (D 8) (R 8) [96,20,72,129,288] 13 :=
  permutation_upper _ _ _ [96,12,80,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14035

theorem m21359_384 : Upper (D 8) (R 8) [96,20,72,129,384] 13 :=
  permutation_upper _ _ _ [96,12,80,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14040

def r21359 : Route 9 := (fun mask => (mask,id))

def c21359 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u21359 : Upper (D 8) (R 8) [96,20,72,129] 13 := by
  apply FastRouting.sound _ _ [96,20,72,129] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r21359 c21359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21359_3
  · exact m21359_33
  · exact m21359_34
  · exact m21359_129
  · exact m21359_130
  · exact m21359_160
  · exact m21359_257
  · exact m21359_258
  · exact m21359_288
  · exact m21359_384

#print axioms u21359
end Delivery.IrregularNine14.P08
