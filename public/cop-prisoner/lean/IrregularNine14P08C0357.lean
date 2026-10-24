import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0210
import IrregularNine14P08C0213
import IrregularNine14P08C0216
import IrregularNine14P08C0218
import IrregularNine14P08C0220
import IrregularNine14P08C0222
import IrregularNine14P08C0223
import IrregularNine14P08C0226
import IrregularNine14P08C0227
import IrregularNine14P08C0228
import IrregularNine14P08C0229
import IrregularNine14P08C0230
import IrregularNine14P08C0231
import IrregularNine14P08C0232
import IrregularNine14P08C0233
import IrregularNine14P08C0234
import IrregularNine14P08C0235
import IrregularNine14P08C0236
import IrregularNine14P08C0237

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m21420_3 : Upper (D 8) (R 8) [96,20,192,288,3] 13 :=
  permutation_upper _ _ _ [96,5,10,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12635

theorem m21420_9 : Upper (D 8) (R 8) [96,20,192,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13588

theorem m21420_10 : Upper (D 8) (R 8) [96,20,192,288,10] 13 :=
  permutation_upper _ _ _ [96,12,18,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13718

theorem m21420_33 : Upper (D 8) (R 8) [96,20,192,288,33] 13 :=
  permutation_upper _ _ _ [96,12,33,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13765

theorem m21420_34 : Upper (D 8) (R 8) [96,20,192,288,34] 13 :=
  permutation_upper _ _ _ [96,12,34,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13839

theorem m21420_40 : Upper (D 8) (R 8) [96,20,192,288,40] 13 :=
  permutation_upper _ _ _ [96,12,48,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13916

theorem m21420_129 : Upper (D 8) (R 8) [96,20,192,288,129] 13 :=
  permutation_upper _ _ _ [96,12,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14097

theorem m21420_130 : Upper (D 8) (R 8) [96,20,192,288,130] 13 :=
  permutation_upper _ _ _ [96,12,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14141

theorem m21420_136 : Upper (D 8) (R 8) [96,20,192,288,136] 13 :=
  permutation_upper _ _ _ [96,12,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14171

theorem m21420_160 : Upper (D 8) (R 8) [96,20,192,288,160] 13 :=
  permutation_upper _ _ _ [96,12,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14210

def r21420 : Route 9 := (fun mask => (mask,id))

def c21420 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21420 : Upper (D 8) (R 8) [96,20,192,288] 13 := by
  apply FastRouting.sound _ _ [96,20,192,288] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21420 c21420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21420_3
  · exact m21420_9
  · exact m21420_10
  · exact m21420_33
  · exact m21420_34
  · exact m21420_40
  · exact m21420_129
  · exact m21420_130
  · exact m21420_136
  · exact m21420_160

theorem m21421_3 : Upper (D 8) (R 8) [96,20,192,384,3] 13 :=
  permutation_upper _ _ _ [96,5,10,192,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12636

theorem m21421_9 : Upper (D 8) (R 8) [96,20,192,384,9] 13 :=
  permutation_upper _ _ _ [96,5,384,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13651

theorem m21421_10 : Upper (D 8) (R 8) [96,20,192,384,10] 13 :=
  permutation_upper _ _ _ [96,12,18,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13719

theorem m21421_33 : Upper (D 8) (R 8) [96,20,192,384,33] 13 :=
  permutation_upper _ _ _ [96,12,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13766

theorem m21421_34 : Upper (D 8) (R 8) [96,20,192,384,34] 13 :=
  permutation_upper _ _ _ [96,12,34,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13840

theorem m21421_40 : Upper (D 8) (R 8) [96,20,192,384,40] 13 :=
  permutation_upper _ _ _ [96,12,48,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13917

def r21421 : Route 9 := (fun mask => (mask,id))

def c21421 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21421 : Upper (D 8) (R 8) [96,20,192,384] 13 := by
  apply FastRouting.sound _ _ [96,20,192,384] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21421 c21421
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21421_3
  · exact m21421_9
  · exact m21421_10
  · exact m21421_33
  · exact m21421_34
  · exact m21421_40

theorem m21422_9 : Upper (D 8) (R 8) [96,20,257,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12815

theorem m21422_33 : Upper (D 8) (R 8) [96,20,257,34,33] 13 :=
  permutation_upper _ _ _ [96,12,33,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13767

theorem m21422_40 : Upper (D 8) (R 8) [96,20,257,34,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13919

theorem m21422_65 : Upper (D 8) (R 8) [96,20,257,34,65] 13 :=
  permutation_upper _ _ _ [96,12,65,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13969

theorem m21422_72 : Upper (D 8) (R 8) [96,20,257,34,72] 13 :=
  permutation_upper _ _ _ [96,12,80,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14027

theorem m21422_96 : Upper (D 8) (R 8) [96,20,257,34,96] 13 :=
  permutation_upper _ _ _ [96,12,96,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14059

theorem m21422_129 : Upper (D 8) (R 8) [96,20,257,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14098

theorem m21422_136 : Upper (D 8) (R 8) [96,20,257,34,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14173

theorem m21422_160 : Upper (D 8) (R 8) [96,20,257,34,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14212

theorem m21422_192 : Upper (D 8) (R 8) [96,20,257,34,192] 13 :=
  permutation_upper _ _ _ [96,12,192,257,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14248

def r21422 : Route 9 := (fun mask => (mask,id))

def c21422 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21422 : Upper (D 8) (R 8) [96,20,257,34] 13 := by
  apply FastRouting.sound _ _ [96,20,257,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21422 c21422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21422_9
  · exact m21422_33
  · exact m21422_40
  · exact m21422_65
  · exact m21422_72
  · exact m21422_96
  · exact m21422_129
  · exact m21422_136
  · exact m21422_160
  · exact m21422_192

theorem m21423_9 : Upper (D 8) (R 8) [96,20,257,66,9] 13 :=
  permutation_upper _ _ _ [96,5,72,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13003

theorem m21423_33 : Upper (D 8) (R 8) [96,20,257,66,33] 13 :=
  permutation_upper _ _ _ [96,12,33,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13768

theorem m21423_40 : Upper (D 8) (R 8) [96,20,257,66,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13921

theorem m21423_129 : Upper (D 8) (R 8) [96,20,257,66,129] 13 :=
  permutation_upper _ _ _ [96,12,129,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14099

theorem m21423_136 : Upper (D 8) (R 8) [96,20,257,66,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14175

theorem m21423_160 : Upper (D 8) (R 8) [96,20,257,66,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14214

def r21423 : Route 9 := (fun mask => (mask,id))

def c21423 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21423 : Upper (D 8) (R 8) [96,20,257,66] 13 := by
  apply FastRouting.sound _ _ [96,20,257,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21423 c21423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21423_9
  · exact m21423_33
  · exact m21423_40
  · exact m21423_129
  · exact m21423_136
  · exact m21423_160

theorem m21424_10 : Upper (D 8) (R 8) [96,20,257,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13707

theorem m21424_34 : Upper (D 8) (R 8) [96,20,257,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13844

theorem m21424_40 : Upper (D 8) (R 8) [96,20,257,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13923

theorem m21424_66 : Upper (D 8) (R 8) [96,20,257,129,66] 13 :=
  permutation_upper _ _ _ [96,12,66,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13995

theorem m21424_72 : Upper (D 8) (R 8) [96,20,257,129,72] 13 :=
  permutation_upper _ _ _ [96,12,80,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14028

theorem m21424_96 : Upper (D 8) (R 8) [96,20,257,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14060

theorem m21424_130 : Upper (D 8) (R 8) [96,20,257,129,130] 13 :=
  permutation_upper _ _ _ [96,12,130,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14145

theorem m21424_136 : Upper (D 8) (R 8) [96,20,257,129,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14177

theorem m21424_160 : Upper (D 8) (R 8) [96,20,257,129,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14216

theorem m21424_192 : Upper (D 8) (R 8) [96,20,257,129,192] 13 :=
  permutation_upper _ _ _ [96,12,192,257,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14249

def r21424 : Route 9 := (fun mask => (mask,id))

def c21424 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21424 : Upper (D 8) (R 8) [96,20,257,129] 13 := by
  apply FastRouting.sound _ _ [96,20,257,129] 13 (by decide) (choices 2) [10,34,40,66,72,96,130,136,160,192] r21424 c21424
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21424_10
  · exact m21424_34
  · exact m21424_40
  · exact m21424_66
  · exact m21424_72
  · exact m21424_96
  · exact m21424_130
  · exact m21424_136
  · exact m21424_160
  · exact m21424_192

theorem m21425_9 : Upper (D 8) (R 8) [96,20,257,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13203

theorem m21425_33 : Upper (D 8) (R 8) [96,20,257,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13769

theorem m21425_40 : Upper (D 8) (R 8) [96,20,257,130,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13924

theorem m21425_65 : Upper (D 8) (R 8) [96,20,257,130,65] 13 :=
  permutation_upper _ _ _ [96,12,65,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13970

theorem m21425_72 : Upper (D 8) (R 8) [96,20,257,130,72] 13 :=
  permutation_upper _ _ _ [96,12,80,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14029

theorem m21425_96 : Upper (D 8) (R 8) [96,20,257,130,96] 13 :=
  permutation_upper _ _ _ [96,12,96,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14061

theorem m21425_129 : Upper (D 8) (R 8) [96,20,257,130,129] 13 :=
  permutation_upper _ _ _ [96,12,129,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14100

theorem m21425_136 : Upper (D 8) (R 8) [96,20,257,130,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14178

theorem m21425_160 : Upper (D 8) (R 8) [96,20,257,130,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14217

theorem m21425_192 : Upper (D 8) (R 8) [96,20,257,130,192] 13 :=
  permutation_upper _ _ _ [96,12,192,257,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14250

def r21425 : Route 9 := (fun mask => (mask,id))

def c21425 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21425 : Upper (D 8) (R 8) [96,20,257,130] 13 := by
  apply FastRouting.sound _ _ [96,20,257,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21425 c21425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21425_9
  · exact m21425_33
  · exact m21425_40
  · exact m21425_65
  · exact m21425_72
  · exact m21425_96
  · exact m21425_129
  · exact m21425_136
  · exact m21425_160
  · exact m21425_192

theorem m21426_3 : Upper (D 8) (R 8) [96,20,257,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12637

theorem m21426_9 : Upper (D 8) (R 8) [96,20,257,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13339

theorem m21426_10 : Upper (D 8) (R 8) [96,20,257,160,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13713

theorem m21426_33 : Upper (D 8) (R 8) [96,20,257,160,33] 13 :=
  permutation_upper _ _ _ [96,12,33,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13770

theorem m21426_34 : Upper (D 8) (R 8) [96,20,257,160,34] 13 :=
  permutation_upper _ _ _ [96,12,34,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13845

theorem m21426_40 : Upper (D 8) (R 8) [96,20,257,160,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13925

theorem m21426_65 : Upper (D 8) (R 8) [96,20,257,160,65] 13 :=
  permutation_upper _ _ _ [96,12,65,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13971

theorem m21426_66 : Upper (D 8) (R 8) [96,20,257,160,66] 13 :=
  permutation_upper _ _ _ [96,12,66,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13996

theorem m21426_72 : Upper (D 8) (R 8) [96,20,257,160,72] 13 :=
  permutation_upper _ _ _ [96,12,80,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14030

theorem m21426_96 : Upper (D 8) (R 8) [96,20,257,160,96] 13 :=
  permutation_upper _ _ _ [96,12,96,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14062

theorem m21426_129 : Upper (D 8) (R 8) [96,20,257,160,129] 13 :=
  permutation_upper _ _ _ [96,12,129,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14101

theorem m21426_130 : Upper (D 8) (R 8) [96,20,257,160,130] 13 :=
  permutation_upper _ _ _ [96,12,130,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14146

theorem m21426_136 : Upper (D 8) (R 8) [96,20,257,160,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14179

theorem m21426_160 : Upper (D 8) (R 8) [96,20,257,160,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14218

theorem m21426_192 : Upper (D 8) (R 8) [96,20,257,160,192] 13 :=
  permutation_upper _ _ _ [96,12,192,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14251

def r21426 : Route 9 := (fun mask => (mask,id))

def c21426 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21426 : Upper (D 8) (R 8) [96,20,257,160] 13 := by
  apply FastRouting.sound _ _ [96,20,257,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r21426 c21426
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21426_3
  · exact m21426_9
  · exact m21426_10
  · exact m21426_33
  · exact m21426_34
  · exact m21426_40
  · exact m21426_65
  · exact m21426_66
  · exact m21426_72
  · exact m21426_96
  · exact m21426_129
  · exact m21426_130
  · exact m21426_136
  · exact m21426_160
  · exact m21426_192

theorem m21427_3 : Upper (D 8) (R 8) [96,20,257,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12638

theorem m21427_9 : Upper (D 8) (R 8) [96,20,257,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,18,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13429

theorem m21427_10 : Upper (D 8) (R 8) [96,20,257,192,10] 13 :=
  permutation_upper _ _ _ [96,12,18,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13717

theorem m21427_33 : Upper (D 8) (R 8) [96,20,257,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13771

theorem m21427_34 : Upper (D 8) (R 8) [96,20,257,192,34] 13 :=
  permutation_upper _ _ _ [96,12,34,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13846

theorem m21427_40 : Upper (D 8) (R 8) [96,20,257,192,40] 13 :=
  permutation_upper _ _ _ [96,12,48,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13926

theorem m21427_129 : Upper (D 8) (R 8) [96,20,257,192,129] 13 :=
  permutation_upper _ _ _ [96,12,129,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14102

theorem m21427_130 : Upper (D 8) (R 8) [96,20,257,192,130] 13 :=
  permutation_upper _ _ _ [96,12,130,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14147

theorem m21427_136 : Upper (D 8) (R 8) [96,20,257,192,136] 13 :=
  permutation_upper _ _ _ [96,12,144,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14180

theorem m21427_160 : Upper (D 8) (R 8) [96,20,257,192,160] 13 :=
  permutation_upper _ _ _ [96,12,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14219

def r21427 : Route 9 := (fun mask => (mask,id))

def c21427 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21427 : Upper (D 8) (R 8) [96,20,257,192] 13 := by
  apply FastRouting.sound _ _ [96,20,257,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21427 c21427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21427_3
  · exact m21427_9
  · exact m21427_10
  · exact m21427_33
  · exact m21427_34
  · exact m21427_40
  · exact m21427_129
  · exact m21427_130
  · exact m21427_136
  · exact m21427_160

theorem m21428_9 : Upper (D 8) (R 8) [96,20,258,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13099

theorem m21428_33 : Upper (D 8) (R 8) [96,20,258,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13772

theorem m21428_40 : Upper (D 8) (R 8) [96,20,258,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13930

theorem m21428_65 : Upper (D 8) (R 8) [96,20,258,129,65] 13 :=
  permutation_upper _ _ _ [96,12,65,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13972

theorem m21428_72 : Upper (D 8) (R 8) [96,20,258,129,72] 13 :=
  permutation_upper _ _ _ [96,12,80,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14031

theorem m21428_96 : Upper (D 8) (R 8) [96,20,258,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14063

theorem m21428_129 : Upper (D 8) (R 8) [96,20,258,129,129] 13 :=
  permutation_upper _ _ _ [96,12,129,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14106

theorem m21428_136 : Upper (D 8) (R 8) [96,20,258,129,136] 13 :=
  permutation_upper _ _ _ [96,12,144,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14184

theorem m21428_160 : Upper (D 8) (R 8) [96,20,258,129,160] 13 :=
  permutation_upper _ _ _ [96,12,160,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14223

theorem m21428_192 : Upper (D 8) (R 8) [96,20,258,129,192] 13 :=
  permutation_upper _ _ _ [96,12,192,258,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14252

def r21428 : Route 9 := (fun mask => (mask,id))

def c21428 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21428 : Upper (D 8) (R 8) [96,20,258,129] 13 := by
  apply FastRouting.sound _ _ [96,20,258,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21428 c21428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21428_9
  · exact m21428_33
  · exact m21428_40
  · exact m21428_65
  · exact m21428_72
  · exact m21428_96
  · exact m21428_129
  · exact m21428_136
  · exact m21428_160
  · exact m21428_192

theorem m21429_9 : Upper (D 8) (R 8) [96,20,258,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13340

theorem m21429_33 : Upper (D 8) (R 8) [96,20,258,160,33] 13 :=
  permutation_upper _ _ _ [96,12,33,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13773

theorem m21429_40 : Upper (D 8) (R 8) [96,20,258,160,40] 13 :=
  permutation_upper _ _ _ [96,12,48,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13931

theorem m21429_65 : Upper (D 8) (R 8) [96,20,258,160,65] 13 :=
  permutation_upper _ _ _ [96,12,65,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13973

theorem m21429_72 : Upper (D 8) (R 8) [96,20,258,160,72] 13 :=
  permutation_upper _ _ _ [96,12,80,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14032

theorem m21429_96 : Upper (D 8) (R 8) [96,20,258,160,96] 13 :=
  permutation_upper _ _ _ [96,12,96,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14064

theorem m21429_129 : Upper (D 8) (R 8) [96,20,258,160,129] 13 :=
  permutation_upper _ _ _ [96,12,129,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14107

theorem m21429_136 : Upper (D 8) (R 8) [96,20,258,160,136] 13 :=
  permutation_upper _ _ _ [96,12,144,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14185

theorem m21429_160 : Upper (D 8) (R 8) [96,20,258,160,160] 13 :=
  permutation_upper _ _ _ [96,12,160,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14224

theorem m21429_192 : Upper (D 8) (R 8) [96,20,258,160,192] 13 :=
  permutation_upper _ _ _ [96,12,192,258,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14253

def r21429 : Route 9 := (fun mask => (mask,id))

def c21429 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21429 : Upper (D 8) (R 8) [96,20,258,160] 13 := by
  apply FastRouting.sound _ _ [96,20,258,160] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21429 c21429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21429_9
  · exact m21429_33
  · exact m21429_40
  · exact m21429_65
  · exact m21429_72
  · exact m21429_96
  · exact m21429_129
  · exact m21429_136
  · exact m21429_160
  · exact m21429_192

theorem m21430_9 : Upper (D 8) (R 8) [96,20,258,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,18,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13430

theorem m21430_33 : Upper (D 8) (R 8) [96,20,258,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13774

theorem m21430_40 : Upper (D 8) (R 8) [96,20,258,192,40] 13 :=
  permutation_upper _ _ _ [96,12,48,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13932

theorem m21430_129 : Upper (D 8) (R 8) [96,20,258,192,129] 13 :=
  permutation_upper _ _ _ [96,12,129,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14108

theorem m21430_136 : Upper (D 8) (R 8) [96,20,258,192,136] 13 :=
  permutation_upper _ _ _ [96,12,144,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14186

theorem m21430_160 : Upper (D 8) (R 8) [96,20,258,192,160] 13 :=
  permutation_upper _ _ _ [96,12,160,258,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14225

def r21430 : Route 9 := (fun mask => (mask,id))

def c21430 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21430 : Upper (D 8) (R 8) [96,20,258,192] 13 := by
  apply FastRouting.sound _ _ [96,20,258,192] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21430 c21430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21430_9
  · exact m21430_33
  · exact m21430_40
  · exact m21430_129
  · exact m21430_136
  · exact m21430_160

theorem m21431_33 : Upper (D 8) (R 8) [96,20,264,34,33] 13 :=
  permutation_upper _ _ _ [96,12,33,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13775

theorem m21431_65 : Upper (D 8) (R 8) [96,20,264,34,65] 13 :=
  permutation_upper _ _ _ [96,12,65,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13974

theorem m21431_96 : Upper (D 8) (R 8) [96,20,264,34,96] 13 :=
  permutation_upper _ _ _ [96,12,96,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14065

theorem m21431_129 : Upper (D 8) (R 8) [96,20,264,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14110

theorem m21431_160 : Upper (D 8) (R 8) [96,20,264,34,160] 13 :=
  permutation_upper _ _ _ [96,12,160,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14227

theorem m21431_192 : Upper (D 8) (R 8) [96,20,264,34,192] 13 :=
  permutation_upper _ _ _ [96,12,192,272,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14255

def r21431 : Route 9 := (fun mask => (mask,id))

def c21431 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21431 : Upper (D 8) (R 8) [96,20,264,34] 13 := by
  apply FastRouting.sound _ _ [96,20,264,34] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21431 c21431
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21431_33
  · exact m21431_65
  · exact m21431_96
  · exact m21431_129
  · exact m21431_160
  · exact m21431_192

def b21432 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 144, targets := 64 }], pairs := [(4,6)], upper := (rows 97 22 268 74 177 161 225 161 417), lower := (rows 97 22 268 74 16 32 64 128 256), losses := [] }

theorem u21432 : Upper (D 8) (R 8) [96,20,264,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21432 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21433_3 : Upper (D 8) (R 8) [96,20,264,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,272,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12642

theorem m21433_33 : Upper (D 8) (R 8) [96,20,264,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13776

theorem m21433_34 : Upper (D 8) (R 8) [96,20,264,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13850

theorem m21433_65 : Upper (D 8) (R 8) [96,20,264,129,65] 13 :=
  permutation_upper _ _ _ [96,12,65,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13975

theorem m21433_66 : Upper (D 8) (R 8) [96,20,264,129,66] 13 :=
  permutation_upper _ _ _ [96,12,66,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13997

theorem m21433_96 : Upper (D 8) (R 8) [96,20,264,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14066

theorem m21433_129 : Upper (D 8) (R 8) [96,20,264,129,129] 13 :=
  permutation_upper _ _ _ [96,12,129,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14114

theorem m21433_130 : Upper (D 8) (R 8) [96,20,264,129,130] 13 :=
  permutation_upper _ _ _ [96,12,130,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14151

theorem m21433_160 : Upper (D 8) (R 8) [96,20,264,129,160] 13 :=
  permutation_upper _ _ _ [96,12,160,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14231

theorem m21433_192 : Upper (D 8) (R 8) [96,20,264,129,192] 13 :=
  permutation_upper _ _ _ [96,12,192,272,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14256

def r21433 : Route 9 := (fun mask => (mask,id))

def c21433 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21433 : Upper (D 8) (R 8) [96,20,264,129] 13 := by
  apply FastRouting.sound _ _ [96,20,264,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21433 c21433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21433_3
  · exact m21433_33
  · exact m21433_34
  · exact m21433_65
  · exact m21433_66
  · exact m21433_96
  · exact m21433_129
  · exact m21433_130
  · exact m21433_160
  · exact m21433_192

theorem m21434_33 : Upper (D 8) (R 8) [96,20,264,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13777

theorem m21434_65 : Upper (D 8) (R 8) [96,20,264,130,65] 13 :=
  permutation_upper _ _ _ [96,12,65,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13976

theorem m21434_96 : Upper (D 8) (R 8) [96,20,264,130,96] 13 :=
  permutation_upper _ _ _ [96,12,96,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14067

theorem m21434_129 : Upper (D 8) (R 8) [96,20,264,130,129] 13 :=
  permutation_upper _ _ _ [96,12,129,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14115

theorem m21434_160 : Upper (D 8) (R 8) [96,20,264,130,160] 13 :=
  permutation_upper _ _ _ [96,12,160,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14232

theorem m21434_192 : Upper (D 8) (R 8) [96,20,264,130,192] 13 :=
  permutation_upper _ _ _ [96,12,192,272,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14257

def r21434 : Route 9 := (fun mask => (mask,id))

def c21434 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21434 : Upper (D 8) (R 8) [96,20,264,130] 13 := by
  apply FastRouting.sound _ _ [96,20,264,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r21434 c21434
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21434_33
  · exact m21434_65
  · exact m21434_96
  · exact m21434_129
  · exact m21434_160
  · exact m21434_192

theorem m21435_3 : Upper (D 8) (R 8) [96,20,264,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12643

theorem m21435_33 : Upper (D 8) (R 8) [96,20,264,160,33] 13 :=
  permutation_upper _ _ _ [96,12,33,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13778

theorem m21435_34 : Upper (D 8) (R 8) [96,20,264,160,34] 13 :=
  permutation_upper _ _ _ [96,12,34,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13851

theorem m21435_65 : Upper (D 8) (R 8) [96,20,264,160,65] 13 :=
  permutation_upper _ _ _ [96,12,65,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13977

theorem m21435_66 : Upper (D 8) (R 8) [96,20,264,160,66] 13 :=
  permutation_upper _ _ _ [96,12,66,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13998

theorem m21435_96 : Upper (D 8) (R 8) [96,20,264,160,96] 13 :=
  permutation_upper _ _ _ [96,12,96,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14068

theorem m21435_129 : Upper (D 8) (R 8) [96,20,264,160,129] 13 :=
  permutation_upper _ _ _ [96,12,129,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14116

theorem m21435_130 : Upper (D 8) (R 8) [96,20,264,160,130] 13 :=
  permutation_upper _ _ _ [96,12,130,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14152

theorem m21435_160 : Upper (D 8) (R 8) [96,20,264,160,160] 13 :=
  permutation_upper _ _ _ [96,12,160,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14233

theorem m21435_192 : Upper (D 8) (R 8) [96,20,264,160,192] 13 :=
  permutation_upper _ _ _ [96,12,192,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14258

def r21435 : Route 9 := (fun mask => (mask,id))

def c21435 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21435 : Upper (D 8) (R 8) [96,20,264,160] 13 := by
  apply FastRouting.sound _ _ [96,20,264,160] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r21435 c21435
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21435_3
  · exact m21435_33
  · exact m21435_34
  · exact m21435_65
  · exact m21435_66
  · exact m21435_96
  · exact m21435_129
  · exact m21435_130
  · exact m21435_160
  · exact m21435_192

theorem m21436_3 : Upper (D 8) (R 8) [96,20,264,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,272,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12644

theorem m21436_33 : Upper (D 8) (R 8) [96,20,264,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13779

theorem m21436_34 : Upper (D 8) (R 8) [96,20,264,192,34] 13 :=
  permutation_upper _ _ _ [96,12,34,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13852

theorem m21436_129 : Upper (D 8) (R 8) [96,20,264,192,129] 13 :=
  permutation_upper _ _ _ [96,12,129,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14117

theorem m21436_130 : Upper (D 8) (R 8) [96,20,264,192,130] 13 :=
  permutation_upper _ _ _ [96,12,130,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14153

theorem m21436_160 : Upper (D 8) (R 8) [96,20,264,192,160] 13 :=
  permutation_upper _ _ _ [96,12,160,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14234

def r21436 : Route 9 := (fun mask => (mask,id))

def c21436 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21436 : Upper (D 8) (R 8) [96,20,264,192] 13 := by
  apply FastRouting.sound _ _ [96,20,264,192] 13 (by decide) (choices 2) [3,33,34,129,130,160] r21436 c21436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21436_3
  · exact m21436_33
  · exact m21436_34
  · exact m21436_129
  · exact m21436_130
  · exact m21436_160

theorem m21437_9 : Upper (D 8) (R 8) [96,20,288,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12816

theorem m21437_65 : Upper (D 8) (R 8) [96,20,288,34,65] 13 :=
  permutation_upper _ _ _ [96,12,65,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13978

theorem m21437_72 : Upper (D 8) (R 8) [96,20,288,34,72] 13 :=
  permutation_upper _ _ _ [96,12,80,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14034

theorem m21437_129 : Upper (D 8) (R 8) [96,20,288,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14119

theorem m21437_136 : Upper (D 8) (R 8) [96,20,288,34,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14188

theorem m21437_192 : Upper (D 8) (R 8) [96,20,288,34,192] 13 :=
  permutation_upper _ _ _ [96,12,192,288,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14260

def r21437 : Route 9 := (fun mask => (mask,id))

def c21437 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21437 : Upper (D 8) (R 8) [96,20,288,34] 13 := by
  apply FastRouting.sound _ _ [96,20,288,34] 13 (by decide) (choices 2) [9,65,72,129,136,192] r21437 c21437
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21437_9
  · exact m21437_65
  · exact m21437_72
  · exact m21437_129
  · exact m21437_136
  · exact m21437_192

theorem m21438_9 : Upper (D 8) (R 8) [96,20,288,66,9] 13 :=
  permutation_upper _ _ _ [96,5,72,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13004

theorem m21438_33 : Upper (D 8) (R 8) [96,20,288,66,33] 13 :=
  permutation_upper _ _ _ [96,12,33,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13780

theorem m21438_40 : Upper (D 8) (R 8) [96,20,288,66,40] 13 :=
  permutation_upper _ _ _ [96,12,48,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13934

theorem m21438_129 : Upper (D 8) (R 8) [96,20,288,66,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14121

theorem m21438_136 : Upper (D 8) (R 8) [96,20,288,66,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14190

theorem m21438_160 : Upper (D 8) (R 8) [96,20,288,66,160] 13 :=
  permutation_upper _ _ _ [96,12,160,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14236

def r21438 : Route 9 := (fun mask => (mask,id))

def c21438 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21438 : Upper (D 8) (R 8) [96,20,288,66] 13 := by
  apply FastRouting.sound _ _ [96,20,288,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21438 c21438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21438_9
  · exact m21438_33
  · exact m21438_40
  · exact m21438_129
  · exact m21438_136
  · exact m21438_160

theorem m21439_3 : Upper (D 8) (R 8) [96,20,288,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,288,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12648

theorem m21439_9 : Upper (D 8) (R 8) [96,20,288,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13100

theorem m21439_10 : Upper (D 8) (R 8) [96,20,288,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13708

theorem m21439_33 : Upper (D 8) (R 8) [96,20,288,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13781

theorem m21439_34 : Upper (D 8) (R 8) [96,20,288,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13853

theorem m21439_40 : Upper (D 8) (R 8) [96,20,288,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13935

theorem m21439_65 : Upper (D 8) (R 8) [96,20,288,129,65] 13 :=
  permutation_upper _ _ _ [96,12,65,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13979

theorem m21439_66 : Upper (D 8) (R 8) [96,20,288,129,66] 13 :=
  permutation_upper _ _ _ [96,12,66,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13999

theorem m21439_72 : Upper (D 8) (R 8) [96,20,288,129,72] 13 :=
  permutation_upper _ _ _ [96,12,80,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14035

theorem m21439_96 : Upper (D 8) (R 8) [96,20,288,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14069

theorem m21439_129 : Upper (D 8) (R 8) [96,20,288,129,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14123

theorem m21439_130 : Upper (D 8) (R 8) [96,20,288,129,130] 13 :=
  permutation_upper _ _ _ [96,12,130,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14157

theorem m21439_136 : Upper (D 8) (R 8) [96,20,288,129,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14192

theorem m21439_160 : Upper (D 8) (R 8) [96,20,288,129,160] 13 :=
  permutation_upper _ _ _ [96,12,160,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14237

theorem m21439_192 : Upper (D 8) (R 8) [96,20,288,129,192] 13 :=
  permutation_upper _ _ _ [96,12,192,288,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14261

def r21439 : Route 9 := (fun mask => (mask,id))

def c21439 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21439 : Upper (D 8) (R 8) [96,20,288,129] 13 := by
  apply FastRouting.sound _ _ [96,20,288,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r21439 c21439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21439_3
  · exact m21439_9
  · exact m21439_10
  · exact m21439_33
  · exact m21439_34
  · exact m21439_40
  · exact m21439_65
  · exact m21439_66
  · exact m21439_72
  · exact m21439_96
  · exact m21439_129
  · exact m21439_130
  · exact m21439_136
  · exact m21439_160
  · exact m21439_192

theorem m21440_9 : Upper (D 8) (R 8) [96,20,288,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13204

theorem m21440_33 : Upper (D 8) (R 8) [96,20,288,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13782

theorem m21440_40 : Upper (D 8) (R 8) [96,20,288,130,40] 13 :=
  permutation_upper _ _ _ [96,12,48,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13936

theorem m21440_65 : Upper (D 8) (R 8) [96,20,288,130,65] 13 :=
  permutation_upper _ _ _ [96,12,65,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13980

theorem m21440_72 : Upper (D 8) (R 8) [96,20,288,130,72] 13 :=
  permutation_upper _ _ _ [96,12,80,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14036

theorem m21440_96 : Upper (D 8) (R 8) [96,20,288,130,96] 13 :=
  permutation_upper _ _ _ [96,12,96,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14070

theorem m21440_129 : Upper (D 8) (R 8) [96,20,288,130,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14124

theorem m21440_136 : Upper (D 8) (R 8) [96,20,288,130,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14193

theorem m21440_160 : Upper (D 8) (R 8) [96,20,288,130,160] 13 :=
  permutation_upper _ _ _ [96,12,160,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14238

theorem m21440_192 : Upper (D 8) (R 8) [96,20,288,130,192] 13 :=
  permutation_upper _ _ _ [96,12,192,288,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14262

def r21440 : Route 9 := (fun mask => (mask,id))

def c21440 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21440 : Upper (D 8) (R 8) [96,20,288,130] 13 := by
  apply FastRouting.sound _ _ [96,20,288,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21440 c21440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21440_9
  · exact m21440_33
  · exact m21440_40
  · exact m21440_65
  · exact m21440_72
  · exact m21440_96
  · exact m21440_129
  · exact m21440_136
  · exact m21440_160
  · exact m21440_192

theorem m21441_3 : Upper (D 8) (R 8) [96,20,288,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12649

theorem m21441_9 : Upper (D 8) (R 8) [96,20,288,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13341

theorem m21441_10 : Upper (D 8) (R 8) [96,20,288,160,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13714

theorem m21441_65 : Upper (D 8) (R 8) [96,20,288,160,65] 13 :=
  permutation_upper _ _ _ [96,12,65,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13981

theorem m21441_66 : Upper (D 8) (R 8) [96,20,288,160,66] 13 :=
  permutation_upper _ _ _ [96,12,66,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14000

theorem m21441_72 : Upper (D 8) (R 8) [96,20,288,160,72] 13 :=
  permutation_upper _ _ _ [96,12,80,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14037

theorem m21441_129 : Upper (D 8) (R 8) [96,20,288,160,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14125

theorem m21441_130 : Upper (D 8) (R 8) [96,20,288,160,130] 13 :=
  permutation_upper _ _ _ [96,12,130,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14158

theorem m21441_136 : Upper (D 8) (R 8) [96,20,288,160,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14194

theorem m21441_192 : Upper (D 8) (R 8) [96,20,288,160,192] 13 :=
  permutation_upper _ _ _ [96,12,192,288,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14263

def r21441 : Route 9 := (fun mask => (mask,id))

def c21441 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21441 : Upper (D 8) (R 8) [96,20,288,160] 13 := by
  apply FastRouting.sound _ _ [96,20,288,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r21441 c21441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21441_3
  · exact m21441_9
  · exact m21441_10
  · exact m21441_65
  · exact m21441_66
  · exact m21441_72
  · exact m21441_129
  · exact m21441_130
  · exact m21441_136
  · exact m21441_192

theorem m21442_3 : Upper (D 8) (R 8) [96,20,288,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12650

theorem m21442_9 : Upper (D 8) (R 8) [96,20,288,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,18,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13431

theorem m21442_10 : Upper (D 8) (R 8) [96,20,288,192,10] 13 :=
  permutation_upper _ _ _ [96,12,18,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13718

theorem m21442_33 : Upper (D 8) (R 8) [96,20,288,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13783

theorem m21442_34 : Upper (D 8) (R 8) [96,20,288,192,34] 13 :=
  permutation_upper _ _ _ [96,12,34,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13854

theorem m21442_40 : Upper (D 8) (R 8) [96,20,288,192,40] 13 :=
  permutation_upper _ _ _ [96,12,48,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13937

theorem m21442_129 : Upper (D 8) (R 8) [96,20,288,192,129] 13 :=
  permutation_upper _ _ _ [96,12,129,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14126

theorem m21442_130 : Upper (D 8) (R 8) [96,20,288,192,130] 13 :=
  permutation_upper _ _ _ [96,12,130,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14159

theorem m21442_136 : Upper (D 8) (R 8) [96,20,288,192,136] 13 :=
  permutation_upper _ _ _ [96,12,144,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14195

theorem m21442_160 : Upper (D 8) (R 8) [96,20,288,192,160] 13 :=
  permutation_upper _ _ _ [96,12,160,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14239

def r21442 : Route 9 := (fun mask => (mask,id))

def c21442 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21442 : Upper (D 8) (R 8) [96,20,288,192] 13 := by
  apply FastRouting.sound _ _ [96,20,288,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21442 c21442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21442_3
  · exact m21442_9
  · exact m21442_10
  · exact m21442_33
  · exact m21442_34
  · exact m21442_40
  · exact m21442_129
  · exact m21442_130
  · exact m21442_136
  · exact m21442_160

theorem m21443_9 : Upper (D 8) (R 8) [96,20,320,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12817

theorem m21443_33 : Upper (D 8) (R 8) [96,20,320,34,33] 13 :=
  permutation_upper _ _ _ [96,12,33,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13784

theorem m21443_40 : Upper (D 8) (R 8) [96,20,320,34,40] 13 :=
  permutation_upper _ _ _ [96,12,48,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13939

theorem m21443_129 : Upper (D 8) (R 8) [96,20,320,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14128

theorem m21443_136 : Upper (D 8) (R 8) [96,20,320,34,136] 13 :=
  permutation_upper _ _ _ [96,12,144,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14197

theorem m21443_160 : Upper (D 8) (R 8) [96,20,320,34,160] 13 :=
  permutation_upper _ _ _ [96,12,160,320,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14241

def r21443 : Route 9 := (fun mask => (mask,id))

def c21443 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21443 : Upper (D 8) (R 8) [96,20,320,34] 13 := by
  apply FastRouting.sound _ _ [96,20,320,34] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21443 c21443
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21443_9
  · exact m21443_33
  · exact m21443_40
  · exact m21443_129
  · exact m21443_136
  · exact m21443_160

theorem m21444_3 : Upper (D 8) (R 8) [96,20,320,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,320,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12651

theorem m21444_9 : Upper (D 8) (R 8) [96,20,320,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13101

theorem m21444_10 : Upper (D 8) (R 8) [96,20,320,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13709

theorem m21444_33 : Upper (D 8) (R 8) [96,20,320,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13785

theorem m21444_34 : Upper (D 8) (R 8) [96,20,320,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13855

theorem m21444_40 : Upper (D 8) (R 8) [96,20,320,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13940

theorem m21444_129 : Upper (D 8) (R 8) [96,20,320,129,129] 13 :=
  permutation_upper _ _ _ [96,12,129,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14129

theorem m21444_130 : Upper (D 8) (R 8) [96,20,320,129,130] 13 :=
  permutation_upper _ _ _ [96,12,130,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14160

theorem m21444_136 : Upper (D 8) (R 8) [96,20,320,129,136] 13 :=
  permutation_upper _ _ _ [96,12,144,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14198

theorem m21444_160 : Upper (D 8) (R 8) [96,20,320,129,160] 13 :=
  permutation_upper _ _ _ [96,12,160,320,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14242

def r21444 : Route 9 := (fun mask => (mask,id))

def c21444 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21444 : Upper (D 8) (R 8) [96,20,320,129] 13 := by
  apply FastRouting.sound _ _ [96,20,320,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21444 c21444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21444_3
  · exact m21444_9
  · exact m21444_10
  · exact m21444_33
  · exact m21444_34
  · exact m21444_40
  · exact m21444_129
  · exact m21444_130
  · exact m21444_136
  · exact m21444_160

theorem m21445_9 : Upper (D 8) (R 8) [96,20,320,130,9] 13 :=
  permutation_upper _ _ _ [96,5,136,18,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13205

theorem m21445_33 : Upper (D 8) (R 8) [96,20,320,130,33] 13 :=
  permutation_upper _ _ _ [96,12,33,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13786

theorem m21445_40 : Upper (D 8) (R 8) [96,20,320,130,40] 13 :=
  permutation_upper _ _ _ [96,12,48,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13941

theorem m21445_129 : Upper (D 8) (R 8) [96,20,320,130,129] 13 :=
  permutation_upper _ _ _ [96,12,129,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14130

theorem m21445_136 : Upper (D 8) (R 8) [96,20,320,130,136] 13 :=
  permutation_upper _ _ _ [96,12,144,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14199

theorem m21445_160 : Upper (D 8) (R 8) [96,20,320,130,160] 13 :=
  permutation_upper _ _ _ [96,12,160,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14243

def r21445 : Route 9 := (fun mask => (mask,id))

def c21445 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21445 : Upper (D 8) (R 8) [96,20,320,130] 13 := by
  apply FastRouting.sound _ _ [96,20,320,130] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21445 c21445
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21445_9
  · exact m21445_33
  · exact m21445_40
  · exact m21445_129
  · exact m21445_136
  · exact m21445_160

theorem m21446_3 : Upper (D 8) (R 8) [96,20,320,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12652

theorem m21446_9 : Upper (D 8) (R 8) [96,20,320,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13342

theorem m21446_10 : Upper (D 8) (R 8) [96,20,320,160,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13715

theorem m21446_33 : Upper (D 8) (R 8) [96,20,320,160,33] 13 :=
  permutation_upper _ _ _ [96,12,33,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13787

theorem m21446_34 : Upper (D 8) (R 8) [96,20,320,160,34] 13 :=
  permutation_upper _ _ _ [96,12,34,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13856

theorem m21446_40 : Upper (D 8) (R 8) [96,20,320,160,40] 13 :=
  permutation_upper _ _ _ [96,12,48,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13942

theorem m21446_129 : Upper (D 8) (R 8) [96,20,320,160,129] 13 :=
  permutation_upper _ _ _ [96,12,129,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14131

theorem m21446_130 : Upper (D 8) (R 8) [96,20,320,160,130] 13 :=
  permutation_upper _ _ _ [96,12,130,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14161

theorem m21446_136 : Upper (D 8) (R 8) [96,20,320,160,136] 13 :=
  permutation_upper _ _ _ [96,12,144,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14200

theorem m21446_160 : Upper (D 8) (R 8) [96,20,320,160,160] 13 :=
  permutation_upper _ _ _ [96,12,160,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14244

def r21446 : Route 9 := (fun mask => (mask,id))

def c21446 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21446 : Upper (D 8) (R 8) [96,20,320,160] 13 := by
  apply FastRouting.sound _ _ [96,20,320,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r21446 c21446
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21446_3
  · exact m21446_9
  · exact m21446_10
  · exact m21446_33
  · exact m21446_34
  · exact m21446_40
  · exact m21446_129
  · exact m21446_130
  · exact m21446_136
  · exact m21446_160

theorem m21447_9 : Upper (D 8) (R 8) [96,20,384,34,9] 13 :=
  permutation_upper _ _ _ [96,5,40,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12818

theorem m21447_33 : Upper (D 8) (R 8) [96,20,384,34,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13788

theorem m21447_40 : Upper (D 8) (R 8) [96,20,384,34,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13944

theorem m21447_65 : Upper (D 8) (R 8) [96,20,384,34,65] 13 :=
  permutation_upper _ _ _ [96,12,65,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13982

theorem m21447_72 : Upper (D 8) (R 8) [96,20,384,34,72] 13 :=
  permutation_upper _ _ _ [96,12,80,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14039

theorem m21447_96 : Upper (D 8) (R 8) [96,20,384,34,96] 13 :=
  permutation_upper _ _ _ [96,12,96,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14071

theorem m21447_129 : Upper (D 8) (R 8) [96,20,384,34,129] 13 :=
  permutation_upper _ _ _ [96,12,129,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14132

theorem m21447_136 : Upper (D 8) (R 8) [96,20,384,34,136] 13 :=
  permutation_upper _ _ _ [96,12,144,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14201

theorem m21447_160 : Upper (D 8) (R 8) [96,20,384,34,160] 13 :=
  permutation_upper _ _ _ [96,12,160,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14245

theorem m21447_192 : Upper (D 8) (R 8) [96,20,384,34,192] 13 :=
  permutation_upper _ _ _ [96,12,192,384,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14264

def r21447 : Route 9 := (fun mask => (mask,id))

def c21447 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u21447 : Upper (D 8) (R 8) [96,20,384,34] 13 := by
  apply FastRouting.sound _ _ [96,20,384,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r21447 c21447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21447_9
  · exact m21447_33
  · exact m21447_40
  · exact m21447_65
  · exact m21447_72
  · exact m21447_96
  · exact m21447_129
  · exact m21447_136
  · exact m21447_160
  · exact m21447_192

theorem m21448_9 : Upper (D 8) (R 8) [96,20,384,66,9] 13 :=
  permutation_upper _ _ _ [96,5,72,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13005

theorem m21448_33 : Upper (D 8) (R 8) [96,20,384,66,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13789

theorem m21448_40 : Upper (D 8) (R 8) [96,20,384,66,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13946

theorem m21448_129 : Upper (D 8) (R 8) [96,20,384,66,129] 13 :=
  permutation_upper _ _ _ [96,12,129,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14133

theorem m21448_136 : Upper (D 8) (R 8) [96,20,384,66,136] 13 :=
  permutation_upper _ _ _ [96,12,144,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14202

theorem m21448_160 : Upper (D 8) (R 8) [96,20,384,66,160] 13 :=
  permutation_upper _ _ _ [96,12,160,384,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14246

def r21448 : Route 9 := (fun mask => (mask,id))

def c21448 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u21448 : Upper (D 8) (R 8) [96,20,384,66] 13 := by
  apply FastRouting.sound _ _ [96,20,384,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r21448 c21448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21448_9
  · exact m21448_33
  · exact m21448_40
  · exact m21448_129
  · exact m21448_136
  · exact m21448_160

theorem m21449_3 : Upper (D 8) (R 8) [96,20,384,129,3] 13 :=
  permutation_upper _ _ _ [96,5,10,384,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12656

theorem m21449_9 : Upper (D 8) (R 8) [96,20,384,129,9] 13 :=
  permutation_upper _ _ _ [96,5,129,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13102

theorem m21449_10 : Upper (D 8) (R 8) [96,20,384,129,10] 13 :=
  permutation_upper _ _ _ [96,12,18,129,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13710

theorem m21449_33 : Upper (D 8) (R 8) [96,20,384,129,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13790

theorem m21449_34 : Upper (D 8) (R 8) [96,20,384,129,34] 13 :=
  permutation_upper _ _ _ [96,12,34,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13860

theorem m21449_40 : Upper (D 8) (R 8) [96,20,384,129,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13948

theorem m21449_65 : Upper (D 8) (R 8) [96,20,384,129,65] 13 :=
  permutation_upper _ _ _ [96,12,65,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13983

theorem m21449_66 : Upper (D 8) (R 8) [96,20,384,129,66] 13 :=
  permutation_upper _ _ _ [96,12,66,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14001

theorem m21449_72 : Upper (D 8) (R 8) [96,20,384,129,72] 13 :=
  permutation_upper _ _ _ [96,12,80,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14040

theorem m21449_96 : Upper (D 8) (R 8) [96,20,384,129,96] 13 :=
  permutation_upper _ _ _ [96,12,96,384,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14072

def r21449 : Route 9 := (fun mask => (mask,id))

def c21449 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21449 : Upper (D 8) (R 8) [96,20,384,129] 13 := by
  apply FastRouting.sound _ _ [96,20,384,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21449 c21449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21449_3
  · exact m21449_9
  · exact m21449_10
  · exact m21449_33
  · exact m21449_34
  · exact m21449_40
  · exact m21449_65
  · exact m21449_66
  · exact m21449_72
  · exact m21449_96

def b21450 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 22 388 138 121 105 105 233 361), lower := (rows 97 22 388 138 16 32 64 128 256), losses := [] }

theorem u21450 : Upper (D 8) (R 8) [96,20,384,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21450 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21451_3 : Upper (D 8) (R 8) [96,20,384,160,3] 13 :=
  permutation_upper _ _ _ [96,5,10,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12657

theorem m21451_9 : Upper (D 8) (R 8) [96,20,384,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13343

theorem m21451_10 : Upper (D 8) (R 8) [96,20,384,160,10] 13 :=
  permutation_upper _ _ _ [96,12,18,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13716

theorem m21451_33 : Upper (D 8) (R 8) [96,20,384,160,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13791

theorem m21451_34 : Upper (D 8) (R 8) [96,20,384,160,34] 13 :=
  permutation_upper _ _ _ [96,12,34,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13861

theorem m21451_40 : Upper (D 8) (R 8) [96,20,384,160,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13950

theorem m21451_65 : Upper (D 8) (R 8) [96,20,384,160,65] 13 :=
  permutation_upper _ _ _ [96,12,65,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13984

theorem m21451_66 : Upper (D 8) (R 8) [96,20,384,160,66] 13 :=
  permutation_upper _ _ _ [96,12,66,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14002

theorem m21451_72 : Upper (D 8) (R 8) [96,20,384,160,72] 13 :=
  permutation_upper _ _ _ [96,12,80,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14042

theorem m21451_96 : Upper (D 8) (R 8) [96,20,384,160,96] 13 :=
  permutation_upper _ _ _ [96,12,96,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14073

def r21451 : Route 9 := (fun mask => (mask,id))

def c21451 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21451 : Upper (D 8) (R 8) [96,20,384,160] 13 := by
  apply FastRouting.sound _ _ [96,20,384,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21451 c21451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21451_3
  · exact m21451_9
  · exact m21451_10
  · exact m21451_33
  · exact m21451_34
  · exact m21451_40
  · exact m21451_65
  · exact m21451_66
  · exact m21451_72
  · exact m21451_96

theorem m21452_3 : Upper (D 8) (R 8) [96,20,384,192,3] 13 :=
  permutation_upper _ _ _ [96,5,10,384,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u12658

theorem m21452_9 : Upper (D 8) (R 8) [96,20,384,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,18,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13432

theorem m21452_10 : Upper (D 8) (R 8) [96,20,384,192,10] 13 :=
  permutation_upper _ _ _ [96,12,18,192,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13719

theorem m21452_33 : Upper (D 8) (R 8) [96,20,384,192,33] 13 :=
  permutation_upper _ _ _ [96,12,33,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13792

theorem m21452_34 : Upper (D 8) (R 8) [96,20,384,192,34] 13 :=
  permutation_upper _ _ _ [96,12,34,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13862

theorem m21452_40 : Upper (D 8) (R 8) [96,20,384,192,40] 13 :=
  permutation_upper _ _ _ [96,12,48,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13951

def r21452 : Route 9 := (fun mask => (mask,id))

def c21452 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21452 : Upper (D 8) (R 8) [96,20,384,192] 13 := by
  apply FastRouting.sound _ _ [96,20,384,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21452 c21452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21452_3
  · exact m21452_9
  · exact m21452_10
  · exact m21452_33
  · exact m21452_34
  · exact m21452_40

def b21453 : PairBound 9 := { available := 409, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 38 76 409 441 473 409 409), lower := (rows 97 35 38 76 16 32 64 128 256), losses := [] }

theorem u21453 : Upper (D 8) (R 8) [96,33,34,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21453 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21454 : PairBound 9 := { available := 476, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 137 476 508 476 476 476), lower := (rows 97 35 38 137 16 32 64 128 256), losses := [] }

theorem u21454 : Upper (D 8) (R 8) [96,33,34,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21454 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21455 : PairBound 9 := { available := 473, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 140 473 505 473 473 473), lower := (rows 97 35 38 140 16 32 64 128 256), losses := [] }

theorem u21455 : Upper (D 8) (R 8) [96,33,34,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21455 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21456 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 200 413 445 477 413 413), lower := (rows 97 35 38 200 16 32 64 128 256), losses := [] }

theorem u21456 : Upper (D 8) (R 8) [96,33,34,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21456 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21457 : PairBound 9 := { available := 220, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 265 220 252 220 220 476), lower := (rows 97 35 38 265 16 32 64 128 256), losses := [] }

theorem u21457 : Upper (D 8) (R 8) [96,33,34,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21457 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21458 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 268 217 249 217 217 473), lower := (rows 97 35 38 268 16 32 64 128 256), losses := [] }

theorem u21458 : Upper (D 8) (R 8) [96,33,34,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21458 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21459 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 328 157 189 221 157 413), lower := (rows 97 35 38 328 16 32 64 128 256), losses := [] }

theorem u21459 : Upper (D 8) (R 8) [96,33,34,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21459 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21460 : PairBound 9 := { available := 221, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 38 392 221 253 221 221 477), lower := (rows 97 35 38 392 16 32 64 128 256), losses := [] }

theorem u21460 : Upper (D 8) (R 8) [96,33,34,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21460 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21461 : PairBound 9 := { available := 405, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 44 74 405 437 469 405 405), lower := (rows 97 35 44 74 16 32 64 128 256), losses := [] }

theorem u21461 : Upper (D 8) (R 8) [96,33,40,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21461 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21462 : PairBound 9 := { available := 470, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 137 470 502 470 470 470), lower := (rows 97 35 44 137 16 32 64 128 256), losses := [] }

theorem u21462 : Upper (D 8) (R 8) [96,33,40,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21462 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21463 : PairBound 9 := { available := 469, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 138 469 501 469 469 469), lower := (rows 97 35 44 138 16 32 64 128 256), losses := [] }

theorem u21463 : Upper (D 8) (R 8) [96,33,40,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21463 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21464 : PairBound 9 := { available := 467, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 140 467 499 467 467 467), lower := (rows 97 35 44 140 16 32 64 128 256), losses := [] }

theorem u21464 : Upper (D 8) (R 8) [96,33,40,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21464 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21465 : PairBound 9 := { available := 407, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 200 407 439 471 407 407), lower := (rows 97 35 44 200 16 32 64 128 256), losses := [] }

theorem u21465 : Upper (D 8) (R 8) [96,33,40,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21465 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21466 : PairBound 9 := { available := 214, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 265 214 246 214 214 470), lower := (rows 97 35 44 265 16 32 64 128 256), losses := [] }

theorem u21466 : Upper (D 8) (R 8) [96,33,40,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21466 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21467 : PairBound 9 := { available := 213, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 266 213 245 213 213 469), lower := (rows 97 35 44 266 16 32 64 128 256), losses := [] }

theorem u21467 : Upper (D 8) (R 8) [96,33,40,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21467 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21468 : PairBound 9 := { available := 211, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 268 211 243 211 211 467), lower := (rows 97 35 44 268 16 32 64 128 256), losses := [] }

theorem u21468 : Upper (D 8) (R 8) [96,33,40,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21468 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21469 : PairBound 9 := { available := 151, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 328 151 183 215 151 407), lower := (rows 97 35 44 328 16 32 64 128 256), losses := [] }

theorem u21469 : Upper (D 8) (R 8) [96,33,40,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21469 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21470 : PairBound 9 := { available := 215, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 44 392 215 247 215 215 471), lower := (rows 97 35 44 392 16 32 64 128 256), losses := [] }

theorem u21470 : Upper (D 8) (R 8) [96,33,40,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21470 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21471 : PairBound 9 := { available := 444, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 137 444 444 508 444 444), lower := (rows 97 35 70 137 16 32 64 128 256), losses := [] }

theorem u21471 : Upper (D 8) (R 8) [96,33,66,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21471 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21472 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 140 441 441 505 441 441), lower := (rows 97 35 70 140 16 32 64 128 256), losses := [] }

theorem u21472 : Upper (D 8) (R 8) [96,33,66,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21472 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21473 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 168 413 445 477 413 413), lower := (rows 97 35 70 168 16 32 64 128 256), losses := [] }

theorem u21473 : Upper (D 8) (R 8) [96,33,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21473 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21474 : PairBound 9 := { available := 188, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 265 188 188 252 188 444), lower := (rows 97 35 70 265 16 32 64 128 256), losses := [] }

theorem u21474 : Upper (D 8) (R 8) [96,33,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21474 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21475 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 268 185 185 249 185 441), lower := (rows 97 35 70 268 16 32 64 128 256), losses := [] }

theorem u21475 : Upper (D 8) (R 8) [96,33,66,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21475 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21476 : PairBound 9 := { available := 157, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 296 157 189 221 157 413), lower := (rows 97 35 70 296 16 32 64 128 256), losses := [] }

theorem u21476 : Upper (D 8) (R 8) [96,33,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21476 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21477 : PairBound 9 := { available := 189, camps := [{ cop := 0, region := 2, targets := 128 }], pairs := [(1,7)], upper := (rows 97 35 70 392 189 189 253 189 445), lower := (rows 97 35 70 392 16 32 64 128 256), losses := [] }

theorem u21477 : Upper (D 8) (R 8) [96,33,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21477 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21478 : PairBound 9 := { available := 438, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 137 438 438 502 438 438), lower := (rows 97 35 76 137 16 32 64 128 256), losses := [] }

theorem u21478 : Upper (D 8) (R 8) [96,33,72,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21478 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21479 : PairBound 9 := { available := 437, camps := [{ cop := 0, region := 2, targets := 64 }], pairs := [(1,6)], upper := (rows 97 35 76 138 437 437 501 437 437), lower := (rows 97 35 76 138 16 32 64 128 256), losses := [] }

theorem u21479 : Upper (D 8) (R 8) [96,33,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21479 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u21479
end Delivery.IrregularNine14.P08
