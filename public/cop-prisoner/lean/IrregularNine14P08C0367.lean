import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0250
import IrregularNine14P08C0252
import IrregularNine14P08C0253
import IrregularNine14P08C0254
import IrregularNine14P08C0255
import IrregularNine14P08C0256
import IrregularNine14P08C0257

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m22020_9 : Upper (D 8) (R 8) [192,5,48,66,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15213

theorem m22020_33 : Upper (D 8) (R 8) [192,5,48,66,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15226

theorem m22020_40 : Upper (D 8) (R 8) [192,5,48,66,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15238

theorem m22020_129 : Upper (D 8) (R 8) [192,5,48,66,129] 13 :=
  permutation_upper _ _ _ [192,5,40,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15245

theorem m22020_136 : Upper (D 8) (R 8) [192,5,48,66,136] 13 :=
  permutation_upper _ _ _ [192,5,40,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15257

theorem m22020_160 : Upper (D 8) (R 8) [192,5,48,66,160] 13 :=
  permutation_upper _ _ _ [192,5,40,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15265

theorem m22020_257 : Upper (D 8) (R 8) [192,5,48,66,257] 13 :=
  permutation_upper _ _ _ [192,5,40,257,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15277

theorem m22020_264 : Upper (D 8) (R 8) [192,5,48,66,264] 13 :=
  permutation_upper _ _ _ [192,5,40,272,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15286

theorem m22020_288 : Upper (D 8) (R 8) [192,5,48,66,288] 13 :=
  permutation_upper _ _ _ [192,5,40,288,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15291

theorem m22020_384 : Upper (D 8) (R 8) [192,5,48,66,384] 13 :=
  permutation_upper _ _ _ [192,5,40,320,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15295

def r22020 : Route 9 := (fun mask => (mask,id))

def c22020 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22020 : Upper (D 8) (R 8) [192,5,48,66] 13 := by
  apply FastRouting.sound _ _ [192,5,48,66] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r22020 c22020
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22020_9
  · exact m22020_33
  · exact m22020_40
  · exact m22020_129
  · exact m22020_136
  · exact m22020_160
  · exact m22020_257
  · exact m22020_264
  · exact m22020_288
  · exact m22020_384

theorem m22021_3 : Upper (D 8) (R 8) [192,5,48,96,3] 13 :=
  permutation_upper _ _ _ [192,5,9,34,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15051

theorem m22021_9 : Upper (D 8) (R 8) [192,5,48,96,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15214

theorem m22021_10 : Upper (D 8) (R 8) [192,5,48,96,10] 13 :=
  permutation_upper _ _ _ [192,5,40,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15220

theorem m22021_33 : Upper (D 8) (R 8) [192,5,48,96,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15227

theorem m22021_34 : Upper (D 8) (R 8) [192,5,48,96,34] 13 :=
  permutation_upper _ _ _ [192,5,40,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15232

theorem m22021_40 : Upper (D 8) (R 8) [192,5,48,96,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15239

theorem m22021_129 : Upper (D 8) (R 8) [192,5,48,96,129] 13 :=
  permutation_upper _ _ _ [192,5,40,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15246

theorem m22021_130 : Upper (D 8) (R 8) [192,5,48,96,130] 13 :=
  permutation_upper _ _ _ [192,5,40,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15251

theorem m22021_136 : Upper (D 8) (R 8) [192,5,48,96,136] 13 :=
  permutation_upper _ _ _ [192,5,40,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15258

theorem m22021_160 : Upper (D 8) (R 8) [192,5,48,96,160] 13 :=
  permutation_upper _ _ _ [192,5,40,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15266

theorem m22021_257 : Upper (D 8) (R 8) [192,5,48,96,257] 13 :=
  permutation_upper _ _ _ [192,5,40,257,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15278

theorem m22021_258 : Upper (D 8) (R 8) [192,5,48,96,258] 13 :=
  permutation_upper _ _ _ [192,5,40,258,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15281

theorem m22021_264 : Upper (D 8) (R 8) [192,5,48,96,264] 13 :=
  permutation_upper _ _ _ [192,5,40,272,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15287

theorem m22021_288 : Upper (D 8) (R 8) [192,5,48,96,288] 13 :=
  permutation_upper _ _ _ [192,5,40,288,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15292

theorem m22021_384 : Upper (D 8) (R 8) [192,5,48,96,384] 13 :=
  permutation_upper _ _ _ [192,5,40,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15296

def r22021 : Route 9 := (fun mask => (mask,id))

def c22021 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22021 : Upper (D 8) (R 8) [192,5,48,96] 13 := by
  apply FastRouting.sound _ _ [192,5,48,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r22021 c22021
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22021_3
  · exact m22021_9
  · exact m22021_10
  · exact m22021_33
  · exact m22021_34
  · exact m22021_40
  · exact m22021_129
  · exact m22021_130
  · exact m22021_136
  · exact m22021_160
  · exact m22021_257
  · exact m22021_258
  · exact m22021_264
  · exact m22021_288
  · exact m22021_384

theorem m22022_10 : Upper (D 8) (R 8) [192,5,48,257,10] 13 :=
  permutation_upper _ _ _ [192,5,40,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15222

theorem m22022_34 : Upper (D 8) (R 8) [192,5,48,257,34] 13 :=
  permutation_upper _ _ _ [192,5,40,34,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15233

theorem m22022_40 : Upper (D 8) (R 8) [192,5,48,257,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15240

theorem m22022_66 : Upper (D 8) (R 8) [192,5,48,257,66] 13 :=
  permutation_upper _ _ _ [192,5,40,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15252

theorem m22022_72 : Upper (D 8) (R 8) [192,5,48,257,72] 13 :=
  permutation_upper _ _ _ [192,5,40,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15259

theorem m22022_96 : Upper (D 8) (R 8) [192,5,48,257,96] 13 :=
  permutation_upper _ _ _ [192,5,40,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15267

theorem m22022_192 : Upper (D 8) (R 8) [192,5,48,257,192] 13 :=
  permutation_upper _ _ _ [192,5,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15273

def r22022 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22022 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22022 : Upper (D 8) (R 8) [192,5,48,257] 13 := by
  apply FastRouting.sound _ _ [192,5,48,257] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r22022 c22022
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22022_10
  · exact m22022_34
  · exact m22022_40
  · exact m22022_66
  · exact m22022_72
  · exact m22022_96
  · exact m22022_192

theorem m22023_9 : Upper (D 8) (R 8) [192,5,48,258,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15215

theorem m22023_33 : Upper (D 8) (R 8) [192,5,48,258,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15228

theorem m22023_40 : Upper (D 8) (R 8) [192,5,48,258,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15241

theorem m22023_65 : Upper (D 8) (R 8) [192,5,48,258,65] 13 :=
  permutation_upper _ _ _ [192,5,40,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15247

theorem m22023_72 : Upper (D 8) (R 8) [192,5,48,258,72] 13 :=
  permutation_upper _ _ _ [192,5,40,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15260

theorem m22023_96 : Upper (D 8) (R 8) [192,5,48,258,96] 13 :=
  permutation_upper _ _ _ [192,5,40,96,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15268

theorem m22023_192 : Upper (D 8) (R 8) [192,5,48,258,192] 13 :=
  permutation_upper _ _ _ [192,5,40,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15274

def r22023 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22023 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22023 : Upper (D 8) (R 8) [192,5,48,258] 13 := by
  apply FastRouting.sound _ _ [192,5,48,258] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22023 c22023
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22023_9
  · exact m22023_33
  · exact m22023_40
  · exact m22023_65
  · exact m22023_72
  · exact m22023_96
  · exact m22023_192

theorem m22024_3 : Upper (D 8) (R 8) [192,5,48,288,3] 13 :=
  permutation_upper _ _ _ [192,5,9,34,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15052

theorem m22024_9 : Upper (D 8) (R 8) [192,5,48,288,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15216

theorem m22024_10 : Upper (D 8) (R 8) [192,5,48,288,10] 13 :=
  permutation_upper _ _ _ [192,5,40,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15223

theorem m22024_33 : Upper (D 8) (R 8) [192,5,48,288,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15229

theorem m22024_34 : Upper (D 8) (R 8) [192,5,48,288,34] 13 :=
  permutation_upper _ _ _ [192,5,40,34,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15234

theorem m22024_40 : Upper (D 8) (R 8) [192,5,48,288,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15242

theorem m22024_65 : Upper (D 8) (R 8) [192,5,48,288,65] 13 :=
  permutation_upper _ _ _ [192,5,40,65,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15248

theorem m22024_66 : Upper (D 8) (R 8) [192,5,48,288,66] 13 :=
  permutation_upper _ _ _ [192,5,40,66,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15253

theorem m22024_72 : Upper (D 8) (R 8) [192,5,48,288,72] 13 :=
  permutation_upper _ _ _ [192,5,40,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15261

theorem m22024_96 : Upper (D 8) (R 8) [192,5,48,288,96] 13 :=
  permutation_upper _ _ _ [192,5,40,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15269

theorem m22024_192 : Upper (D 8) (R 8) [192,5,48,288,192] 13 :=
  permutation_upper _ _ _ [192,5,40,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15275

def r22024 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22024 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22024 : Upper (D 8) (R 8) [192,5,48,288] 13 := by
  apply FastRouting.sound _ _ [192,5,48,288] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r22024 c22024
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22024_3
  · exact m22024_9
  · exact m22024_10
  · exact m22024_33
  · exact m22024_34
  · exact m22024_40
  · exact m22024_65
  · exact m22024_66
  · exact m22024_72
  · exact m22024_96
  · exact m22024_192

theorem m22025_3 : Upper (D 8) (R 8) [192,5,48,320,3] 13 :=
  permutation_upper _ _ _ [192,5,9,34,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15053

theorem m22025_9 : Upper (D 8) (R 8) [192,5,48,320,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15217

theorem m22025_10 : Upper (D 8) (R 8) [192,5,48,320,10] 13 :=
  permutation_upper _ _ _ [192,5,40,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15224

theorem m22025_33 : Upper (D 8) (R 8) [192,5,48,320,33] 13 :=
  permutation_upper _ _ _ [192,5,40,33,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15230

theorem m22025_34 : Upper (D 8) (R 8) [192,5,48,320,34] 13 :=
  permutation_upper _ _ _ [192,5,40,34,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15235

theorem m22025_40 : Upper (D 8) (R 8) [192,5,48,320,40] 13 :=
  permutation_upper _ _ _ [192,5,40,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15243

theorem m22025_129 : Upper (D 8) (R 8) [192,5,48,320,129] 13 :=
  permutation_upper _ _ _ [192,5,40,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15249

theorem m22025_130 : Upper (D 8) (R 8) [192,5,48,320,130] 13 :=
  permutation_upper _ _ _ [192,5,40,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15254

theorem m22025_136 : Upper (D 8) (R 8) [192,5,48,320,136] 13 :=
  permutation_upper _ _ _ [192,5,40,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15262

theorem m22025_160 : Upper (D 8) (R 8) [192,5,48,320,160] 13 :=
  permutation_upper _ _ _ [192,5,40,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15270

def r22025 : Route 9 := (fun mask => (mask,id))

def c22025 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22025 : Upper (D 8) (R 8) [192,5,48,320] 13 := by
  apply FastRouting.sound _ _ [192,5,48,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22025 c22025
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22025_3
  · exact m22025_9
  · exact m22025_10
  · exact m22025_33
  · exact m22025_34
  · exact m22025_40
  · exact m22025_129
  · exact m22025_130
  · exact m22025_136
  · exact m22025_160

def b22026 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 26 440 424 488 424 424), lower := (rows 193 7 69 26 16 32 64 128 256), losses := [] }

theorem u22026 : Upper (D 8) (R 8) [192,5,65,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22026 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22027 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 42 440 440 504 440 440), lower := (rows 193 7 69 42 16 32 64 128 256), losses := [] }

theorem u22027 : Upper (D 8) (R 8) [192,5,65,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22027 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22028 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 138 312 312 376 440 312), lower := (rows 193 7 69 138 16 32 64 128 256), losses := [] }

theorem u22028 : Upper (D 8) (R 8) [192,5,65,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22028 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22029 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 168 314 314 378 442 314), lower := (rows 193 7 69 168 16 32 64 128 256), losses := [] }

theorem u22029 : Upper (D 8) (R 8) [192,5,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22029 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22030 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 266 184 184 248 184 440), lower := (rows 193 7 69 266 16 32 64 128 256), losses := [] }

theorem u22030 : Upper (D 8) (R 8) [192,5,65,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22030 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22031 : PairBound 9 := { available := 186, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 296 186 186 250 186 442), lower := (rows 193 7 69 296 16 32 64 128 256), losses := [] }

theorem u22031 : Upper (D 8) (R 8) [192,5,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22031 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22032 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 69 392 58 58 122 186 314), lower := (rows 193 7 69 392 16 32 64 128 256), losses := [] }

theorem u22032 : Upper (D 8) (R 8) [192,5,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22032 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22033 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 41 440 440 504 440 440), lower := (rows 193 7 70 41 16 32 64 128 256), losses := [] }

theorem u22033 : Upper (D 8) (R 8) [192,5,66,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22033 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22034 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 168 313 313 377 441 313), lower := (rows 193 7 70 168 16 32 64 128 256), losses := [] }

theorem u22034 : Upper (D 8) (R 8) [192,5,66,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22034 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22035 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 265 184 184 248 184 440), lower := (rows 193 7 70 265 16 32 64 128 256), losses := [] }

theorem u22035 : Upper (D 8) (R 8) [192,5,66,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22035 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22036 : PairBound 9 := { available := 185, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 296 185 185 249 185 441), lower := (rows 193 7 70 296 16 32 64 128 256), losses := [] }

theorem u22036 : Upper (D 8) (R 8) [192,5,66,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22036 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22037 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 70 392 57 57 121 185 313), lower := (rows 193 7 70 392 16 32 64 128 256), losses := [] }

theorem u22037 : Upper (D 8) (R 8) [192,5,66,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22037 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22038 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 26 433 417 481 417 417), lower := (rows 193 7 76 26 16 32 64 128 256), losses := [] }

theorem u22038 : Upper (D 8) (R 8) [192,5,72,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22038 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22039 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 41 434 434 498 434 434), lower := (rows 193 7 76 41 16 32 64 128 256), losses := [] }

theorem u22039 : Upper (D 8) (R 8) [192,5,72,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22039 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22040 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 42 433 433 497 433 433), lower := (rows 193 7 76 42 16 32 64 128 256), losses := [] }

theorem u22040 : Upper (D 8) (R 8) [192,5,72,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22040 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22041 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 76 138 305 305 369 433 305), lower := (rows 193 7 76 138 16 32 64 128 256), losses := [] }

theorem u22041 : Upper (D 8) (R 8) [192,5,72,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22041 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22042 : PairBound 9 := { available := 307, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 168 307 307 371 435 307), lower := (rows 193 7 76 168 16 32 64 128 256), losses := [] }

theorem u22042 : Upper (D 8) (R 8) [192,5,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22042 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22043 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 265 178 178 242 178 434), lower := (rows 193 7 76 265 16 32 64 128 256), losses := [] }

theorem u22043 : Upper (D 8) (R 8) [192,5,72,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22043 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22044 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 266 177 177 241 177 433), lower := (rows 193 7 76 266 16 32 64 128 256), losses := [] }

theorem u22044 : Upper (D 8) (R 8) [192,5,72,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22044 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22045 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 296 179 179 243 179 435), lower := (rows 193 7 76 296 16 32 64 128 256), losses := [] }

theorem u22045 : Upper (D 8) (R 8) [192,5,72,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22045 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22046 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 76 392 51 51 115 179 307), lower := (rows 193 7 76 392 16 32 64 128 256), losses := [] }

theorem u22046 : Upper (D 8) (R 8) [192,5,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22046 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22047 : PairBound 9 := { available := 426, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 41 442 426 490 426 426), lower := (rows 193 7 84 41 16 32 64 128 256), losses := [] }

theorem u22047 : Upper (D 8) (R 8) [192,5,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22047 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22048 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 42 441 425 489 425 425), lower := (rows 193 7 84 42 16 32 64 128 256), losses := [] }

theorem u22048 : Upper (D 8) (R 8) [192,5,80,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22048 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22049 : PairBound 9 := { available := 297, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 138 313 297 361 425 297), lower := (rows 193 7 84 138 16 32 64 128 256), losses := [] }

theorem u22049 : Upper (D 8) (R 8) [192,5,80,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22049 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22050 : PairBound 9 := { available := 299, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 168 315 299 363 427 299), lower := (rows 193 7 84 168 16 32 64 128 256), losses := [] }

theorem u22050 : Upper (D 8) (R 8) [192,5,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22050 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22051 : PairBound 9 := { available := 170, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 265 186 170 234 170 426), lower := (rows 193 7 84 265 16 32 64 128 256), losses := [] }

theorem u22051 : Upper (D 8) (R 8) [192,5,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22051 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22052 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 266 185 169 233 169 425), lower := (rows 193 7 84 266 16 32 64 128 256), losses := [] }

theorem u22052 : Upper (D 8) (R 8) [192,5,80,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22052 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22053 : PairBound 9 := { available := 171, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 296 187 171 235 171 427), lower := (rows 193 7 84 296 16 32 64 128 256), losses := [] }

theorem u22053 : Upper (D 8) (R 8) [192,5,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22053 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22054 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 424, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 84 392 59 43 107 171 299), lower := (rows 193 7 84 392 16 32 64 128 256), losses := [] }

theorem u22054 : Upper (D 8) (R 8) [192,5,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22054 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22055 : PairBound 9 := { available := 425, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 26 441 425 489 425 425), lower := (rows 193 7 100 26 16 32 64 128 256), losses := [] }

theorem u22055 : Upper (D 8) (R 8) [192,5,96,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22055 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22056 : PairBound 9 := { available := 442, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 41 442 442 506 442 442), lower := (rows 193 7 100 41 16 32 64 128 256), losses := [] }

theorem u22056 : Upper (D 8) (R 8) [192,5,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22056 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22057 : PairBound 9 := { available := 441, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 42 441 441 505 441 441), lower := (rows 193 7 100 42 16 32 64 128 256), losses := [] }

theorem u22057 : Upper (D 8) (R 8) [192,5,96,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22057 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22058 : PairBound 9 := { available := 313, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 138 313 313 377 441 313), lower := (rows 193 7 100 138 16 32 64 128 256), losses := [] }

theorem u22058 : Upper (D 8) (R 8) [192,5,96,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22058 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22059 : PairBound 9 := { available := 315, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 168 315 315 379 443 315), lower := (rows 193 7 100 168 16 32 64 128 256), losses := [] }

theorem u22059 : Upper (D 8) (R 8) [192,5,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22059 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22060 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 265 186 186 250 186 442), lower := (rows 193 7 100 265 16 32 64 128 256), losses := [] }

theorem u22060 : Upper (D 8) (R 8) [192,5,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22060 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22061 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 266 185 185 249 185 441), lower := (rows 193 7 100 266 16 32 64 128 256), losses := [] }

theorem u22061 : Upper (D 8) (R 8) [192,5,96,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22061 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22062 : PairBound 9 := { available := 187, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 296 187 187 251 187 443), lower := (rows 193 7 100 296 16 32 64 128 256), losses := [] }

theorem u22062 : Upper (D 8) (R 8) [192,5,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22062 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22063 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 440, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 100 392 59 59 123 187 315), lower := (rows 193 7 100 392 16 32 64 128 256), losses := [] }

theorem u22063 : Upper (D 8) (R 8) [192,5,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22063 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22064 : PairBound 9 := { available := 297, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 26 313 297 361 425 297), lower := (rows 193 7 196 26 16 32 64 128 256), losses := [] }

theorem u22064 : Upper (D 8) (R 8) [192,5,192,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22064 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22065 : PairBound 9 := { available := 314, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 41 314 314 378 442 314), lower := (rows 193 7 196 41 16 32 64 128 256), losses := [] }

theorem u22065 : Upper (D 8) (R 8) [192,5,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22065 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22066 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 42 313 313 377 441 313), lower := (rows 193 7 196 42 16 32 64 128 256), losses := [] }

theorem u22066 : Upper (D 8) (R 8) [192,5,192,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22066 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22067 : PairBound 9 := { available := 58, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 265 58 58 122 186 314), lower := (rows 193 7 196 265 16 32 64 128 256), losses := [] }

theorem u22067 : Upper (D 8) (R 8) [192,5,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22067 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22068 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 266 57 57 121 185 313), lower := (rows 193 7 196 266 16 32 64 128 256), losses := [] }

theorem u22068 : Upper (D 8) (R 8) [192,5,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22068 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22069 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 196 296 59 59 123 187 315), lower := (rows 193 7 196 296 16 32 64 128 256), losses := [] }

theorem u22069 : Upper (D 8) (R 8) [192,5,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22069 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22070 : PairBound 9 := { available := 232, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 26 248 232 232 232 488), lower := (rows 193 7 261 26 16 32 64 128 256), losses := [] }

theorem u22070 : Upper (D 8) (R 8) [192,5,257,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22070 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22071 : PairBound 9 := { available := 248, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 42 248 248 248 248 504), lower := (rows 193 7 261 42 16 32 64 128 256), losses := [] }

theorem u22071 : Upper (D 8) (R 8) [192,5,257,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22071 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22072 : PairBound 9 := { available := 184, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 74 184 184 248 184 440), lower := (rows 193 7 261 74 16 32 64 128 256), losses := [] }

theorem u22072 : Upper (D 8) (R 8) [192,5,257,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22072 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22073 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 261 104 186 186 250 186 442), lower := (rows 193 7 261 104 16 32 64 128 256), losses := [] }

theorem u22073 : Upper (D 8) (R 8) [192,5,257,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22073 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22074 : PairBound 9 := { available := 232, camps := [{ cop := 3, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 262 25 248 232 232 232 488), lower := (rows 193 7 262 25 16 32 64 128 256), losses := [] }

theorem u22074 : Upper (D 8) (R 8) [192,5,258,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22074 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22075 : PairBound 9 := { available := 248, camps := [{ cop := 3, region := 208, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 262 41 248 248 248 248 504), lower := (rows 193 7 262 41 16 32 64 128 256), losses := [] }

theorem u22075 : Upper (D 8) (R 8) [192,5,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22075 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22076_9 : Upper (D 8) (R 8) [192,5,258,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15176

theorem m22076_33 : Upper (D 8) (R 8) [192,5,258,48,33] 13 :=
  permutation_upper _ _ _ [192,5,258,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15445

def r22076 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22076 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22076 : Upper (D 8) (R 8) [192,5,258,48] 13 := by
  apply FastRouting.sound _ _ [192,5,258,48] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22076 c22076
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22076_9
  · exact m22076_33
  · exact u15448
  · exact u15449
  · exact u15450
  · exact u15451
  · exact u15452

def b22077 : PairBound 9 := { available := 184, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 262 73 184 184 248 184 440), lower := (rows 193 7 262 73 16 32 64 128 256), losses := [] }

theorem u22077 : Upper (D 8) (R 8) [192,5,258,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22077 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22078_9 : Upper (D 8) (R 8) [192,5,258,80,9] 13 :=
  permutation_upper _ _ _ [192,5,66,17,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15318

theorem m22078_33 : Upper (D 8) (R 8) [192,5,258,80,33] 13 :=
  permutation_upper _ _ _ [192,5,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15446

theorem m22078_40 : Upper (D 8) (R 8) [192,5,258,80,40] 13 :=
  permutation_upper _ _ _ [192,5,258,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15450

theorem m22078_129 : Upper (D 8) (R 8) [192,5,258,80,129] 13 :=
  permutation_upper _ _ _ [192,5,258,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15453

def r22078 : Route 9 := (fun mask => (mask,id))

def c22078 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22078 : Upper (D 8) (R 8) [192,5,258,80] 13 := by
  apply FastRouting.sound _ _ [192,5,258,80] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22078 c22078
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22078_9
  · exact m22078_33
  · exact m22078_40
  · exact m22078_129
  · exact u15455
  · exact u15456

theorem m22079_9 : Upper (D 8) (R 8) [192,5,258,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,17,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15384

theorem m22079_33 : Upper (D 8) (R 8) [192,5,258,96,33] 13 :=
  permutation_upper _ _ _ [192,5,258,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15447

theorem m22079_40 : Upper (D 8) (R 8) [192,5,258,96,40] 13 :=
  permutation_upper _ _ _ [192,5,258,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15451

theorem m22079_129 : Upper (D 8) (R 8) [192,5,258,96,129] 13 :=
  permutation_upper _ _ _ [192,5,258,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15454

theorem m22079_136 : Upper (D 8) (R 8) [192,5,258,96,136] 13 :=
  permutation_upper _ _ _ [192,5,258,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15456

def r22079 : Route 9 := (fun mask => (mask,id))

def c22079 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22079 : Upper (D 8) (R 8) [192,5,258,96] 13 := by
  apply FastRouting.sound _ _ [192,5,258,96] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22079 c22079
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22079_9
  · exact m22079_33
  · exact m22079_40
  · exact m22079_129
  · exact m22079_136
  · exact u15457

#print axioms u22079
end Delivery.IrregularNine14.P08
