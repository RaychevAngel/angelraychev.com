import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0043
import IrregularNine14P10C0044
import IrregularNine14P10C0045
import IrregularNine14P10C0046
import IrregularNine14P10C0047
import IrregularNine14P10C0048
import IrregularNine14P10C0049
import IrregularNine14P10C0050
import IrregularNine14P10C0051
import IrregularNine14P10C0052
import IrregularNine14P10C0053
import IrregularNine14P10C0054
import IrregularNine14P10C0055
import IrregularNine14P10C0056
import IrregularNine14P10C0057
import IrregularNine14P10C0058
import IrregularNine14P10C0059

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m3600_5 : Upper (D 10) (R 10) [66,136,320,5] 13 :=
  permutation_upper _ _ _ [6,72,192,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2703

theorem m3600_17 : Upper (D 10) (R 10) [66,136,320,17] 13 :=
  permutation_upper _ _ _ [18,68,129,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2858

theorem m3600_20 : Upper (D 10) (R 10) [66,136,320,20] 13 :=
  permutation_upper _ _ _ [18,192,72,257] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2943

theorem m3600_33 : Upper (D 10) (R 10) [66,136,320,33] 13 :=
  permutation_upper _ _ _ [34,68,129,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3070

theorem m3600_36 : Upper (D 10) (R 10) [66,136,320,36] 13 :=
  permutation_upper _ _ _ [34,192,72,257] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3188

theorem m3600_48 : Upper (D 10) (R 10) [66,136,320,48] 13 :=
  permutation_upper _ _ _ [48,65,130,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3231

theorem m3600_129 : Upper (D 10) (R 10) [66,136,320,129] 13 :=
  permutation_upper _ _ _ [66,68,129,384] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3261

theorem m3600_132 : Upper (D 10) (R 10) [66,136,320,132] 13 :=
  permutation_upper _ _ _ [66,68,384,129] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3268

theorem m3600_144 : Upper (D 10) (R 10) [66,136,320,144] 13 :=
  permutation_upper _ _ _ [66,80,129,384] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3273

theorem m3600_160 : Upper (D 10) (R 10) [66,136,320,160] 13 :=
  permutation_upper _ _ _ [66,96,129,384] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3281

theorem m3600_257 : Upper (D 10) (R 10) [66,136,320,257] 13 :=
  permutation_upper _ _ _ [66,132,257,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3319

theorem m3600_260 : Upper (D 10) (R 10) [66,136,320,260] 13 :=
  permutation_upper _ _ _ [66,132,264,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3323

theorem m3600_272 : Upper (D 10) (R 10) [66,136,320,272] 13 :=
  permutation_upper _ _ _ [66,132,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3328

theorem m3600_288 : Upper (D 10) (R 10) [66,136,320,288] 13 :=
  permutation_upper _ _ _ [66,132,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3337

theorem m3600_384 : Upper (D 10) (R 10) [66,136,320,384] 13 :=
  permutation_upper _ _ _ [66,132,384,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3344

def r3600 : Route 9 := (fun mask => (mask,id))

def c3600 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3600 : Upper (D 10) (R 10) [66,136,320] 13 := by
  apply FastRouting.sound _ _ [66,136,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r3600 c3600
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3600_5
  · exact m3600_17
  · exact m3600_20
  · exact m3600_33
  · exact m3600_36
  · exact m3600_48
  · exact m3600_129
  · exact m3600_132
  · exact m3600_144
  · exact m3600_160
  · exact m3600_257
  · exact m3600_260
  · exact m3600_272
  · exact m3600_288
  · exact m3600_384

theorem m3601_5 : Upper (D 10) (R 10) [66,136,384,5] 13 :=
  permutation_upper _ _ _ [6,72,384,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2712

theorem m3601_17 : Upper (D 10) (R 10) [66,136,384,17] 13 :=
  permutation_upper _ _ _ [18,68,129,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2859

theorem m3601_20 : Upper (D 10) (R 10) [66,136,384,20] 13 :=
  permutation_upper _ _ _ [18,192,65,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2938

theorem m3601_33 : Upper (D 10) (R 10) [66,136,384,33] 13 :=
  permutation_upper _ _ _ [34,68,129,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3071

theorem m3601_36 : Upper (D 10) (R 10) [66,136,384,36] 13 :=
  permutation_upper _ _ _ [34,192,65,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3182

theorem m3601_48 : Upper (D 10) (R 10) [66,136,384,48] 13 :=
  permutation_upper _ _ _ [48,65,130,320] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3230

theorem m3601_65 : Upper (D 10) (R 10) [66,136,384,65] 13 :=
  permutation_upper _ _ _ [66,68,129,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3261

theorem m3601_68 : Upper (D 10) (R 10) [66,136,384,68] 13 :=
  permutation_upper _ _ _ [66,132,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3306

theorem m3601_80 : Upper (D 10) (R 10) [66,136,384,80] 13 :=
  permutation_upper _ _ _ [66,132,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3310

theorem m3601_96 : Upper (D 10) (R 10) [66,136,384,96] 13 :=
  permutation_upper _ _ _ [66,132,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3314

theorem m3601_257 : Upper (D 10) (R 10) [66,136,384,257] 13 :=
  permutation_upper _ _ _ [66,132,257,192] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3319

theorem m3601_260 : Upper (D 10) (R 10) [66,136,384,260] 13 :=
  permutation_upper _ _ _ [66,132,192,257] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3315

theorem m3601_272 : Upper (D 10) (R 10) [66,136,384,272] 13 :=
  permutation_upper _ _ _ [66,132,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3329

theorem m3601_288 : Upper (D 10) (R 10) [66,136,384,288] 13 :=
  permutation_upper _ _ _ [66,132,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3338

theorem m3601_320 : Upper (D 10) (R 10) [66,136,384,320] 13 :=
  permutation_upper _ _ _ [66,132,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3341

def r3601 : Route 9 := (fun mask => (mask,id))

def c3601 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3601 : Upper (D 10) (R 10) [66,136,384] 13 := by
  apply FastRouting.sound _ _ [66,136,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r3601 c3601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3601_5
  · exact m3601_17
  · exact m3601_20
  · exact m3601_33
  · exact m3601_36
  · exact m3601_48
  · exact m3601_65
  · exact m3601_68
  · exact m3601_80
  · exact m3601_96
  · exact m3601_257
  · exact m3601_260
  · exact m3601_272
  · exact m3601_288
  · exact m3601_320

theorem m3602_5 : Upper (D 10) (R 10) [66,160,72,5] 13 :=
  permutation_upper _ _ _ [6,65,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2623

theorem m3602_17 : Upper (D 10) (R 10) [66,160,72,17] 13 :=
  permutation_upper _ _ _ [18,68,160,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2867

theorem m3602_20 : Upper (D 10) (R 10) [66,160,72,20] 13 :=
  permutation_upper _ _ _ [18,65,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2823

theorem m3602_33 : Upper (D 10) (R 10) [66,160,72,33] 13 :=
  permutation_upper _ _ _ [34,68,160,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3094

theorem m3602_36 : Upper (D 10) (R 10) [66,160,72,36] 13 :=
  permutation_upper _ _ _ [34,65,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3011

theorem m3602_48 : Upper (D 10) (R 10) [66,160,72,48] 13 :=
  permutation_upper _ _ _ [48,65,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3220

theorem m3602_129 : Upper (D 10) (R 10) [66,160,72,129] 13 :=
  permutation_upper _ _ _ [66,132,72,160] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3303

theorem m3602_132 : Upper (D 10) (R 10) [66,160,72,132] 13 :=
  permutation_upper _ _ _ [66,129,72,160] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3286

theorem m3602_144 : Upper (D 10) (R 10) [66,160,72,144] 13 :=
  permutation_upper _ _ _ [66,144,72,160] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3345

theorem m3602_257 : Upper (D 10) (R 10) [66,160,72,257] 13 :=
  permutation_upper _ _ _ [66,132,72,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3305

theorem m3602_260 : Upper (D 10) (R 10) [66,160,72,260] 13 :=
  permutation_upper _ _ _ [66,129,72,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3288

theorem m3602_272 : Upper (D 10) (R 10) [66,160,72,272] 13 :=
  permutation_upper _ _ _ [66,144,72,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3346

def r3602 : Route 9 := (fun mask => (mask,id))

def c3602 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3602 : Upper (D 10) (R 10) [66,160,72] 13 := by
  apply FastRouting.sound _ _ [66,160,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r3602 c3602
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3602_5
  · exact m3602_17
  · exact m3602_20
  · exact m3602_33
  · exact m3602_36
  · exact m3602_48
  · exact m3602_129
  · exact m3602_132
  · exact m3602_144
  · exact u3363
  · exact m3602_257
  · exact m3602_260
  · exact m3602_272
  · exact u3364
  · exact u3365

theorem m3603_5 : Upper (D 10) (R 10) [66,160,96,5] 13 :=
  permutation_upper _ _ _ [6,72,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2672

theorem m3603_17 : Upper (D 10) (R 10) [66,160,96,17] 13 :=
  permutation_upper _ _ _ [18,68,160,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2868

theorem m3603_20 : Upper (D 10) (R 10) [66,160,96,20] 13 :=
  permutation_upper _ _ _ [18,96,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2904

theorem m3603_33 : Upper (D 10) (R 10) [66,160,96,33] 13 :=
  permutation_upper _ _ _ [34,68,160,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3096

theorem m3603_36 : Upper (D 10) (R 10) [66,160,96,36] 13 :=
  permutation_upper _ _ _ [34,96,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3154

theorem m3603_48 : Upper (D 10) (R 10) [66,160,96,48] 13 :=
  permutation_upper _ _ _ [48,68,160,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3243

theorem m3603_129 : Upper (D 10) (R 10) [66,160,96,129] 13 :=
  permutation_upper _ _ _ [66,132,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3311

theorem m3603_257 : Upper (D 10) (R 10) [66,160,96,257] 13 :=
  permutation_upper _ _ _ [66,132,288,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3333

def r3603 : Route 9 := (fun mask => (mask,id))

def c3603 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3603 : Upper (D 10) (R 10) [66,160,96] 13 := by
  apply FastRouting.sound _ _ [66,160,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r3603 c3603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3603_5
  · exact m3603_17
  · exact m3603_20
  · exact m3603_33
  · exact m3603_36
  · exact m3603_48
  · exact m3603_129
  · exact u3368
  · exact u3369
  · exact u3370
  · exact m3603_257
  · exact u3371
  · exact u3372
  · exact u3373
  · exact u3374

theorem m3604_5 : Upper (D 10) (R 10) [66,160,136,5] 13 :=
  permutation_upper _ _ _ [6,65,136,96] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2631

theorem m3604_17 : Upper (D 10) (R 10) [66,160,136,17] 13 :=
  permutation_upper _ _ _ [18,68,160,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2869

theorem m3604_20 : Upper (D 10) (R 10) [66,160,136,20] 13 :=
  permutation_upper _ _ _ [18,65,96,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2825

theorem m3604_33 : Upper (D 10) (R 10) [66,160,136,33] 13 :=
  permutation_upper _ _ _ [34,68,160,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3097

theorem m3604_36 : Upper (D 10) (R 10) [66,160,136,36] 13 :=
  permutation_upper _ _ _ [34,65,96,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3016

theorem m3604_48 : Upper (D 10) (R 10) [66,160,136,48] 13 :=
  permutation_upper _ _ _ [48,65,96,132] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3223

theorem m3604_65 : Upper (D 10) (R 10) [66,160,136,65] 13 :=
  permutation_upper _ _ _ [66,68,160,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3264

theorem m3604_68 : Upper (D 10) (R 10) [66,160,136,68] 13 :=
  permutation_upper _ _ _ [66,129,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3286

theorem m3604_80 : Upper (D 10) (R 10) [66,160,136,80] 13 :=
  permutation_upper _ _ _ [66,144,96,132] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3348

theorem m3604_96 : Upper (D 10) (R 10) [66,160,136,96] 13 :=
  permutation_upper _ _ _ [66,160,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3368

theorem m3604_257 : Upper (D 10) (R 10) [66,160,136,257] 13 :=
  permutation_upper _ _ _ [66,132,264,96] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3321

theorem m3604_260 : Upper (D 10) (R 10) [66,160,136,260] 13 :=
  permutation_upper _ _ _ [66,129,96,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3293

theorem m3604_272 : Upper (D 10) (R 10) [66,160,136,272] 13 :=
  permutation_upper _ _ _ [66,144,96,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3350

theorem m3604_288 : Upper (D 10) (R 10) [66,160,136,288] 13 :=
  permutation_upper _ _ _ [66,160,96,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3371

def r3604 : Route 9 := (fun mask => (mask,id))

def c3604 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3604 : Upper (D 10) (R 10) [66,160,136] 13 := by
  apply FastRouting.sound _ _ [66,160,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r3604 c3604
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3604_5
  · exact m3604_17
  · exact m3604_20
  · exact m3604_33
  · exact m3604_36
  · exact m3604_48
  · exact m3604_65
  · exact m3604_68
  · exact m3604_80
  · exact m3604_96
  · exact m3604_257
  · exact m3604_260
  · exact m3604_272
  · exact m3604_288
  · exact u3375

def b3605 : PairBound 9 := { available := 381, camps := [{ cop := 1, region := 4, targets := 320 }], pairs := [(2,6),(2,8)], upper := (rows 67 162 164 381 381 381 381 509 381), lower := (rows 67 162 164 8 16 32 64 128 256), losses := [] }

theorem u3605 : Upper (D 10) (R 10) [66,160,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3605 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3606_5 : Upper (D 10) (R 10) [66,160,192,5] 13 :=
  permutation_upper _ _ _ [6,72,192,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2702

theorem m3606_17 : Upper (D 10) (R 10) [66,160,192,17] 13 :=
  permutation_upper _ _ _ [18,68,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2870

theorem m3606_20 : Upper (D 10) (R 10) [66,160,192,20] 13 :=
  permutation_upper _ _ _ [18,192,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2942

theorem m3606_33 : Upper (D 10) (R 10) [66,160,192,33] 13 :=
  permutation_upper _ _ _ [34,68,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3100

theorem m3606_36 : Upper (D 10) (R 10) [66,160,192,36] 13 :=
  permutation_upper _ _ _ [34,192,72,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3187

theorem m3606_48 : Upper (D 10) (R 10) [66,160,192,48] 13 :=
  permutation_upper _ _ _ [48,68,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3244

theorem m3606_257 : Upper (D 10) (R 10) [66,160,192,257] 13 :=
  permutation_upper _ _ _ [66,132,288,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3338

def r3606 : Route 9 := (fun mask => (mask,id))

def c3606 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3606 : Upper (D 10) (R 10) [66,160,192] 13 := by
  apply FastRouting.sound _ _ [66,160,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r3606 c3606
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3606_5
  · exact m3606_17
  · exact m3606_20
  · exact m3606_33
  · exact m3606_36
  · exact m3606_48
  · exact m3606_257
  · exact u3381
  · exact u3382
  · exact u3383

theorem m3607_5 : Upper (D 10) (R 10) [66,160,264,5] 13 :=
  permutation_upper _ _ _ [6,65,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2636

theorem m3607_17 : Upper (D 10) (R 10) [66,160,264,17] 13 :=
  permutation_upper _ _ _ [18,68,160,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2871

theorem m3607_20 : Upper (D 10) (R 10) [66,160,264,20] 13 :=
  permutation_upper _ _ _ [18,65,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2829

theorem m3607_33 : Upper (D 10) (R 10) [66,160,264,33] 13 :=
  permutation_upper _ _ _ [34,68,160,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3101

theorem m3607_36 : Upper (D 10) (R 10) [66,160,264,36] 13 :=
  permutation_upper _ _ _ [34,65,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3025

theorem m3607_48 : Upper (D 10) (R 10) [66,160,264,48] 13 :=
  permutation_upper _ _ _ [48,65,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3233

theorem m3607_65 : Upper (D 10) (R 10) [66,160,264,65] 13 :=
  permutation_upper _ _ _ [66,68,160,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3265

theorem m3607_68 : Upper (D 10) (R 10) [66,160,264,68] 13 :=
  permutation_upper _ _ _ [66,129,72,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3288

theorem m3607_80 : Upper (D 10) (R 10) [66,160,264,80] 13 :=
  permutation_upper _ _ _ [66,144,136,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3353

theorem m3607_96 : Upper (D 10) (R 10) [66,160,264,96] 13 :=
  permutation_upper _ _ _ [66,160,96,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3371

theorem m3607_129 : Upper (D 10) (R 10) [66,160,264,129] 13 :=
  permutation_upper _ _ _ [66,132,96,257] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3312

theorem m3607_132 : Upper (D 10) (R 10) [66,160,264,132] 13 :=
  permutation_upper _ _ _ [66,129,96,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3293

theorem m3607_144 : Upper (D 10) (R 10) [66,160,264,144] 13 :=
  permutation_upper _ _ _ [66,144,160,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3355

theorem m3607_160 : Upper (D 10) (R 10) [66,160,264,160] 13 :=
  permutation_upper _ _ _ [66,160,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3378

theorem m3607_192 : Upper (D 10) (R 10) [66,160,264,192] 13 :=
  permutation_upper _ _ _ [66,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3381

theorem m3607_257 : Upper (D 10) (R 10) [66,160,264,257] 13 :=
  permutation_upper _ _ _ [66,68,136,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3263

theorem m3607_260 : Upper (D 10) (R 10) [66,160,264,260] 13 :=
  permutation_upper _ _ _ [66,65,136,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3256

theorem m3607_272 : Upper (D 10) (R 10) [66,160,264,272] 13 :=
  permutation_upper _ _ _ [66,80,136,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3275

theorem m3607_288 : Upper (D 10) (R 10) [66,160,264,288] 13 :=
  permutation_upper _ _ _ [66,96,136,288] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3283

def r3607 : Route 9 := (fun mask => (mask,id))

def c3607 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3607 : Upper (D 10) (R 10) [66,160,264] 13 := by
  apply FastRouting.sound _ _ [66,160,264] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r3607 c3607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3607_5
  · exact m3607_17
  · exact m3607_20
  · exact m3607_33
  · exact m3607_36
  · exact m3607_48
  · exact m3607_65
  · exact m3607_68
  · exact m3607_80
  · exact m3607_96
  · exact m3607_129
  · exact m3607_132
  · exact m3607_144
  · exact m3607_160
  · exact m3607_192
  · exact m3607_257
  · exact m3607_260
  · exact m3607_272
  · exact m3607_288
  · exact u3384
  · exact u3385

theorem m3608_5 : Upper (D 10) (R 10) [66,160,288,5] 13 :=
  permutation_upper _ _ _ [6,72,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2696

theorem m3608_17 : Upper (D 10) (R 10) [66,160,288,17] 13 :=
  permutation_upper _ _ _ [18,68,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2872

theorem m3608_20 : Upper (D 10) (R 10) [66,160,288,20] 13 :=
  permutation_upper _ _ _ [18,96,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2917

theorem m3608_33 : Upper (D 10) (R 10) [66,160,288,33] 13 :=
  permutation_upper _ _ _ [34,68,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3103

theorem m3608_36 : Upper (D 10) (R 10) [66,160,288,36] 13 :=
  permutation_upper _ _ _ [34,96,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3166

theorem m3608_48 : Upper (D 10) (R 10) [66,160,288,48] 13 :=
  permutation_upper _ _ _ [48,68,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3245

theorem m3608_65 : Upper (D 10) (R 10) [66,160,288,65] 13 :=
  permutation_upper _ _ _ [66,68,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3266

theorem m3608_68 : Upper (D 10) (R 10) [66,160,288,68] 13 :=
  permutation_upper _ _ _ [66,160,72,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3364

theorem m3608_80 : Upper (D 10) (R 10) [66,160,288,80] 13 :=
  permutation_upper _ _ _ [66,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3366

theorem m3608_96 : Upper (D 10) (R 10) [66,160,288,96] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3608_129 : Upper (D 10) (R 10) [66,160,288,129] 13 :=
  permutation_upper _ _ _ [66,132,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3313

theorem m3608_132 : Upper (D 10) (R 10) [66,160,288,132] 13 :=
  permutation_upper _ _ _ [66,160,96,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3371

theorem m3608_144 : Upper (D 10) (R 10) [66,160,288,144] 13 :=
  permutation_upper _ _ _ [66,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3376

theorem m3608_160 : Upper (D 10) (R 10) [66,160,288,160] 13 :=
  permutation_upper _ _ _ [66,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3379

theorem m3608_192 : Upper (D 10) (R 10) [66,160,288,192] 13 :=
  permutation_upper _ _ _ [66,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3383

theorem m3608_257 : Upper (D 10) (R 10) [66,160,288,257] 13 :=
  permutation_upper _ _ _ [66,132,288,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3331

theorem m3608_260 : Upper (D 10) (R 10) [66,160,288,260] 13 :=
  permutation_upper _ _ _ [66,96,136,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3283

theorem m3608_272 : Upper (D 10) (R 10) [66,160,288,272] 13 :=
  permutation_upper _ _ _ [66,160,272,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3386

def r3608 : Route 9 := (fun mask => (mask,id))

def c3608 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3608 : Upper (D 10) (R 10) [66,160,288] 13 := by
  apply FastRouting.sound _ _ [66,160,288] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,129,132,144,160,192,257,260,272,288,320,384] r3608 c3608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3608_5
  · exact m3608_17
  · exact m3608_20
  · exact m3608_33
  · exact m3608_36
  · exact m3608_48
  · exact m3608_65
  · exact m3608_68
  · exact m3608_80
  · exact m3608_96
  · exact m3608_129
  · exact m3608_132
  · exact m3608_144
  · exact m3608_160
  · exact m3608_192
  · exact m3608_257
  · exact m3608_260
  · exact m3608_272
  · exact u3389
  · exact u3390
  · exact u3391

theorem m3609_5 : Upper (D 10) (R 10) [66,160,320,5] 13 :=
  permutation_upper _ _ _ [6,72,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2704

theorem m3609_17 : Upper (D 10) (R 10) [66,160,320,17] 13 :=
  permutation_upper _ _ _ [18,68,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2873

theorem m3609_20 : Upper (D 10) (R 10) [66,160,320,20] 13 :=
  permutation_upper _ _ _ [18,192,72,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2945

theorem m3609_33 : Upper (D 10) (R 10) [66,160,320,33] 13 :=
  permutation_upper _ _ _ [34,68,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3104

theorem m3609_36 : Upper (D 10) (R 10) [66,160,320,36] 13 :=
  permutation_upper _ _ _ [34,192,72,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3191

theorem m3609_48 : Upper (D 10) (R 10) [66,160,320,48] 13 :=
  permutation_upper _ _ _ [48,68,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3246

theorem m3609_129 : Upper (D 10) (R 10) [66,160,320,129] 13 :=
  permutation_upper _ _ _ [66,132,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3314

theorem m3609_132 : Upper (D 10) (R 10) [66,160,320,132] 13 :=
  permutation_upper _ _ _ [66,160,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3375

theorem m3609_144 : Upper (D 10) (R 10) [66,160,320,144] 13 :=
  permutation_upper _ _ _ [66,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3377

theorem m3609_160 : Upper (D 10) (R 10) [66,160,320,160] 13 :=
  permutation_upper _ _ _ [66,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3380

theorem m3609_257 : Upper (D 10) (R 10) [66,160,320,257] 13 :=
  permutation_upper _ _ _ [66,132,288,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3334

theorem m3609_260 : Upper (D 10) (R 10) [66,160,320,260] 13 :=
  permutation_upper _ _ _ [66,160,264,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3384

theorem m3609_272 : Upper (D 10) (R 10) [66,160,320,272] 13 :=
  permutation_upper _ _ _ [66,160,272,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3387

theorem m3609_288 : Upper (D 10) (R 10) [66,160,320,288] 13 :=
  permutation_upper _ _ _ [66,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3390

def r3609 : Route 9 := (fun mask => (mask,id))

def c3609 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3609 : Upper (D 10) (R 10) [66,160,320] 13 := by
  apply FastRouting.sound _ _ [66,160,320] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,257,260,272,288,384] r3609 c3609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3609_5
  · exact m3609_17
  · exact m3609_20
  · exact m3609_33
  · exact m3609_36
  · exact m3609_48
  · exact m3609_129
  · exact m3609_132
  · exact m3609_144
  · exact m3609_160
  · exact m3609_257
  · exact m3609_260
  · exact m3609_272
  · exact m3609_288
  · exact u3392

theorem m3610_5 : Upper (D 10) (R 10) [66,160,384,5] 13 :=
  permutation_upper _ _ _ [6,72,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2714

theorem m3610_17 : Upper (D 10) (R 10) [66,160,384,17] 13 :=
  permutation_upper _ _ _ [18,68,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2874

theorem m3610_20 : Upper (D 10) (R 10) [66,160,384,20] 13 :=
  permutation_upper _ _ _ [18,192,96,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2949

theorem m3610_33 : Upper (D 10) (R 10) [66,160,384,33] 13 :=
  permutation_upper _ _ _ [34,68,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3105

theorem m3610_36 : Upper (D 10) (R 10) [66,160,384,36] 13 :=
  permutation_upper _ _ _ [34,192,96,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3200

theorem m3610_48 : Upper (D 10) (R 10) [66,160,384,48] 13 :=
  permutation_upper _ _ _ [48,68,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3247

theorem m3610_65 : Upper (D 10) (R 10) [66,160,384,65] 13 :=
  permutation_upper _ _ _ [66,68,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3267

theorem m3610_68 : Upper (D 10) (R 10) [66,160,384,68] 13 :=
  permutation_upper _ _ _ [66,160,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3365

theorem m3610_80 : Upper (D 10) (R 10) [66,160,384,80] 13 :=
  permutation_upper _ _ _ [66,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3367

theorem m3610_96 : Upper (D 10) (R 10) [66,160,384,96] 13 :=
  permutation_upper _ _ _ [66,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3374

theorem m3610_257 : Upper (D 10) (R 10) [66,160,384,257] 13 :=
  permutation_upper _ _ _ [66,132,288,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3337

theorem m3610_260 : Upper (D 10) (R 10) [66,160,384,260] 13 :=
  permutation_upper _ _ _ [66,160,264,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3385

theorem m3610_272 : Upper (D 10) (R 10) [66,160,384,272] 13 :=
  permutation_upper _ _ _ [66,160,272,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3388

theorem m3610_288 : Upper (D 10) (R 10) [66,160,384,288] 13 :=
  permutation_upper _ _ _ [66,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3391

theorem m3610_320 : Upper (D 10) (R 10) [66,160,384,320] 13 :=
  permutation_upper _ _ _ [66,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3392

def r3610 : Route 9 := (fun mask => (mask,id))

def c3610 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3610 : Upper (D 10) (R 10) [66,160,384] 13 := by
  apply FastRouting.sound _ _ [66,160,384] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r3610 c3610
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3610_5
  · exact m3610_17
  · exact m3610_20
  · exact m3610_33
  · exact m3610_36
  · exact m3610_48
  · exact m3610_65
  · exact m3610_68
  · exact m3610_80
  · exact m3610_96
  · exact m3610_257
  · exact m3610_260
  · exact m3610_272
  · exact m3610_288
  · exact m3610_320

def b3611 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 194 164 317 317 317 381 445 317), lower := (rows 67 194 164 8 16 32 64 128 256), losses := [] }

theorem u3611 : Upper (D 10) (R 10) [66,192,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3611 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3612 : PairBound 9 := { available := 445, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 194 292 445 445 445 509 445 445), lower := (rows 67 194 292 8 16 32 64 128 256), losses := [] }

theorem u3612 : Upper (D 10) (R 10) [66,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3612 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3613 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 194 388 317 317 317 381 445 317), lower := (rows 67 194 388 8 16 32 64 128 256), losses := [] }

theorem u3613 : Upper (D 10) (R 10) [66,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3613 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3614_5 : Upper (D 10) (R 10) [66,384,72,5] 13 :=
  permutation_upper _ _ _ [6,65,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2624

theorem m3614_17 : Upper (D 10) (R 10) [66,384,72,17] 13 :=
  permutation_upper _ _ _ [18,68,384,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2882

theorem m3614_20 : Upper (D 10) (R 10) [66,384,72,20] 13 :=
  permutation_upper _ _ _ [18,65,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2824

theorem m3614_33 : Upper (D 10) (R 10) [66,384,72,33] 13 :=
  permutation_upper _ _ _ [34,68,384,65] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3112

theorem m3614_36 : Upper (D 10) (R 10) [66,384,72,36] 13 :=
  permutation_upper _ _ _ [34,65,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3012

theorem m3614_48 : Upper (D 10) (R 10) [66,384,72,48] 13 :=
  permutation_upper _ _ _ [48,65,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3221

theorem m3614_129 : Upper (D 10) (R 10) [66,384,72,129] 13 :=
  permutation_upper _ _ _ [66,132,72,384] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3306

theorem m3614_132 : Upper (D 10) (R 10) [66,384,72,132] 13 :=
  permutation_upper _ _ _ [66,129,72,384] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3289

theorem m3614_144 : Upper (D 10) (R 10) [66,384,72,144] 13 :=
  permutation_upper _ _ _ [66,144,72,384] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3347

theorem m3614_160 : Upper (D 10) (R 10) [66,384,72,160] 13 :=
  permutation_upper _ _ _ [66,160,72,384] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3365

def r3614 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3614 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3614 : Upper (D 10) (R 10) [66,384,72] 13 := by
  apply FastRouting.sound _ _ [66,384,72] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,384] r3614 c3614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3614_5
  · exact m3614_17
  · exact m3614_20
  · exact m3614_33
  · exact m3614_36
  · exact m3614_48
  · exact m3614_129
  · exact m3614_132
  · exact m3614_144
  · exact m3614_160
  · exact u3395

theorem m3615_5 : Upper (D 10) (R 10) [66,384,96,5] 13 :=
  permutation_upper _ _ _ [6,72,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2673

theorem m3615_17 : Upper (D 10) (R 10) [66,384,96,17] 13 :=
  permutation_upper _ _ _ [18,68,384,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2883

theorem m3615_20 : Upper (D 10) (R 10) [66,384,96,20] 13 :=
  permutation_upper _ _ _ [18,96,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2905

theorem m3615_33 : Upper (D 10) (R 10) [66,384,96,33] 13 :=
  permutation_upper _ _ _ [34,68,384,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3114

theorem m3615_36 : Upper (D 10) (R 10) [66,384,96,36] 13 :=
  permutation_upper _ _ _ [34,96,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3155

theorem m3615_48 : Upper (D 10) (R 10) [66,384,96,48] 13 :=
  permutation_upper _ _ _ [48,68,384,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3248

theorem m3615_129 : Upper (D 10) (R 10) [66,384,96,129] 13 :=
  permutation_upper _ _ _ [66,132,320,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3339

theorem m3615_132 : Upper (D 10) (R 10) [66,384,96,132] 13 :=
  permutation_upper _ _ _ [66,160,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3375

def r3615 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3615 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3615 : Upper (D 10) (R 10) [66,384,96] 13 := by
  apply FastRouting.sound _ _ [66,384,96] 13 (by decide) (choices 2) [5,17,20,33,36,48,129,132,144,160,384] r3615 c3615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3615_5
  · exact m3615_17
  · exact m3615_20
  · exact m3615_33
  · exact m3615_36
  · exact m3615_48
  · exact m3615_129
  · exact m3615_132
  · exact u3397
  · exact u3398
  · exact u3399

theorem m3616_5 : Upper (D 10) (R 10) [66,384,136,5] 13 :=
  permutation_upper _ _ _ [6,65,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2637

theorem m3616_17 : Upper (D 10) (R 10) [66,384,136,17] 13 :=
  permutation_upper _ _ _ [18,68,384,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2884

theorem m3616_20 : Upper (D 10) (R 10) [66,384,136,20] 13 :=
  permutation_upper _ _ _ [18,65,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2830

theorem m3616_33 : Upper (D 10) (R 10) [66,384,136,33] 13 :=
  permutation_upper _ _ _ [34,68,384,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3115

theorem m3616_36 : Upper (D 10) (R 10) [66,384,136,36] 13 :=
  permutation_upper _ _ _ [34,65,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3026

theorem m3616_48 : Upper (D 10) (R 10) [66,384,136,48] 13 :=
  permutation_upper _ _ _ [48,65,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3234

theorem m3616_65 : Upper (D 10) (R 10) [66,384,136,65] 13 :=
  permutation_upper _ _ _ [66,68,384,129] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3268

theorem m3616_68 : Upper (D 10) (R 10) [66,384,136,68] 13 :=
  permutation_upper _ _ _ [66,129,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3289

theorem m3616_80 : Upper (D 10) (R 10) [66,384,136,80] 13 :=
  permutation_upper _ _ _ [66,144,136,320] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3354

theorem m3616_96 : Upper (D 10) (R 10) [66,384,136,96] 13 :=
  permutation_upper _ _ _ [66,160,136,320] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3375

theorem m3616_257 : Upper (D 10) (R 10) [66,384,136,257] 13 :=
  permutation_upper _ _ _ [66,132,264,192] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3322

theorem m3616_260 : Upper (D 10) (R 10) [66,384,136,260] 13 :=
  permutation_upper _ _ _ [66,129,192,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3296

theorem m3616_272 : Upper (D 10) (R 10) [66,384,136,272] 13 :=
  permutation_upper _ _ _ [66,144,192,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3358

theorem m3616_288 : Upper (D 10) (R 10) [66,384,136,288] 13 :=
  permutation_upper _ _ _ [66,160,192,260] (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3381

def r3616 : Route 9 := (fun mask => (mask,id))

def c3616 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3616 : Upper (D 10) (R 10) [66,384,136] 13 := by
  apply FastRouting.sound _ _ [66,384,136] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r3616 c3616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3616_5
  · exact m3616_17
  · exact m3616_20
  · exact m3616_33
  · exact m3616_36
  · exact m3616_48
  · exact m3616_65
  · exact m3616_68
  · exact m3616_80
  · exact m3616_96
  · exact m3616_257
  · exact m3616_260
  · exact m3616_272
  · exact m3616_288
  · exact u3400

theorem m3617_5 : Upper (D 10) (R 10) [66,384,160,5] 13 :=
  permutation_upper _ _ _ [6,72,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2698

theorem m3617_17 : Upper (D 10) (R 10) [66,384,160,17] 13 :=
  permutation_upper _ _ _ [18,68,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2885

theorem m3617_20 : Upper (D 10) (R 10) [66,384,160,20] 13 :=
  permutation_upper _ _ _ [18,96,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2918

theorem m3617_33 : Upper (D 10) (R 10) [66,384,160,33] 13 :=
  permutation_upper _ _ _ [34,68,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3117

theorem m3617_36 : Upper (D 10) (R 10) [66,384,160,36] 13 :=
  permutation_upper _ _ _ [34,96,136,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3167

theorem m3617_48 : Upper (D 10) (R 10) [66,384,160,48] 13 :=
  permutation_upper _ _ _ [48,68,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3249

theorem m3617_65 : Upper (D 10) (R 10) [66,384,160,65] 13 :=
  permutation_upper _ _ _ [66,68,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3269

theorem m3617_68 : Upper (D 10) (R 10) [66,384,160,68] 13 :=
  permutation_upper _ _ _ [66,160,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3365

theorem m3617_80 : Upper (D 10) (R 10) [66,384,160,80] 13 :=
  permutation_upper _ _ _ [66,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3396

theorem m3617_96 : Upper (D 10) (R 10) [66,384,160,96] 13 :=
  permutation_upper _ _ _ [66,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3398

theorem m3617_257 : Upper (D 10) (R 10) [66,384,160,257] 13 :=
  permutation_upper _ _ _ [66,132,320,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3340

theorem m3617_260 : Upper (D 10) (R 10) [66,384,160,260] 13 :=
  permutation_upper _ _ _ [66,160,192,260] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3381

theorem m3617_272 : Upper (D 10) (R 10) [66,384,160,272] 13 :=
  permutation_upper _ _ _ [66,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3401

def r3617 : Route 9 := (fun mask => (mask,id))

def c3617 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3617 : Upper (D 10) (R 10) [66,384,160] 13 := by
  apply FastRouting.sound _ _ [66,384,160] 13 (by decide) (choices 2) [5,17,20,33,36,48,65,68,80,96,257,260,272,288,320] r3617 c3617
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3617_5
  · exact m3617_17
  · exact m3617_20
  · exact m3617_33
  · exact m3617_36
  · exact m3617_48
  · exact m3617_65
  · exact m3617_68
  · exact m3617_80
  · exact m3617_96
  · exact m3617_257
  · exact m3617_260
  · exact m3617_272
  · exact u3403
  · exact u3404

theorem m3618_5 : Upper (D 10) (R 10) [66,384,192,5] 13 :=
  permutation_upper _ _ _ [6,72,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2705

theorem m3618_17 : Upper (D 10) (R 10) [66,384,192,17] 13 :=
  permutation_upper _ _ _ [18,68,384,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2886

theorem m3618_20 : Upper (D 10) (R 10) [66,384,192,20] 13 :=
  permutation_upper _ _ _ [18,192,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2946

theorem m3618_33 : Upper (D 10) (R 10) [66,384,192,33] 13 :=
  permutation_upper _ _ _ [34,68,384,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3118

theorem m3618_36 : Upper (D 10) (R 10) [66,384,192,36] 13 :=
  permutation_upper _ _ _ [34,192,72,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3192

theorem m3618_48 : Upper (D 10) (R 10) [66,384,192,48] 13 :=
  permutation_upper _ _ _ [48,68,384,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3250

theorem m3618_257 : Upper (D 10) (R 10) [66,384,192,257] 13 :=
  permutation_upper _ _ _ [66,132,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3341

theorem m3618_260 : Upper (D 10) (R 10) [66,384,192,260] 13 :=
  permutation_upper _ _ _ [66,384,136,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3400

theorem m3618_272 : Upper (D 10) (R 10) [66,384,192,272] 13 :=
  permutation_upper _ _ _ [66,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3402

theorem m3618_288 : Upper (D 10) (R 10) [66,384,192,288] 13 :=
  permutation_upper _ _ _ [66,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3404

def r3618 : Route 9 := (fun mask => (mask,id))

def c3618 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3618 : Upper (D 10) (R 10) [66,384,192] 13 := by
  apply FastRouting.sound _ _ [66,384,192] 13 (by decide) (choices 2) [5,17,20,33,36,48,257,260,272,288] r3618 c3618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3618_5
  · exact m3618_17
  · exact m3618_20
  · exact m3618_33
  · exact m3618_36
  · exact m3618_48
  · exact m3618_257
  · exact m3618_260
  · exact m3618_272
  · exact m3618_288

def b3619 : PairBound 9 := { available := 125, camps := [{ cop := 1, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 67 386 388 125 125 125 125 253 381), lower := (rows 67 386 388 8 16 32 64 128 256), losses := [] }

theorem u3619 : Upper (D 10) (R 10) [66,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3619 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3620_3 : Upper (D 10) (R 10) [72,96,160,3] 13 :=
  permutation_upper _ _ _ [6,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2627

theorem m3620_5 : Upper (D 10) (R 10) [72,96,160,5] 13 :=
  permutation_upper _ _ _ [6,65,160,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2647

theorem m3620_6 : Upper (D 10) (R 10) [72,96,160,6] 13 :=
  permutation_upper _ _ _ [6,96,160,65] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2751

theorem m3620_17 : Upper (D 10) (R 10) [72,96,160,17] 13 :=
  permutation_upper _ _ _ [18,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2826

theorem m3620_18 : Upper (D 10) (R 10) [72,96,160,18] 13 :=
  permutation_upper _ _ _ [18,96,65,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2900

theorem m3620_20 : Upper (D 10) (R 10) [72,96,160,20] 13 :=
  permutation_upper _ _ _ [18,96,129,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2910

theorem m3620_33 : Upper (D 10) (R 10) [72,96,160,33] 13 :=
  permutation_upper _ _ _ [34,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3017

theorem m3620_34 : Upper (D 10) (R 10) [72,96,160,34] 13 :=
  permutation_upper _ _ _ [34,96,65,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3150

theorem m3620_36 : Upper (D 10) (R 10) [72,96,160,36] 13 :=
  permutation_upper _ _ _ [34,96,129,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3159

theorem m3620_48 : Upper (D 10) (R 10) [72,96,160,48] 13 :=
  permutation_upper _ _ _ [48,65,96,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3224

theorem m3620_129 : Upper (D 10) (R 10) [72,96,160,129] 13 :=
  permutation_upper _ _ _ [66,129,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3292

theorem m3620_130 : Upper (D 10) (R 10) [72,96,160,130] 13 :=
  permutation_upper _ _ _ [66,132,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3311

theorem m3620_132 : Upper (D 10) (R 10) [72,96,160,132] 13 :=
  permutation_upper _ _ _ [66,96,129,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3278

theorem m3620_144 : Upper (D 10) (R 10) [72,96,160,144] 13 :=
  permutation_upper _ _ _ [66,144,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3349

theorem m3620_160 : Upper (D 10) (R 10) [72,96,160,160] 13 :=
  permutation_upper _ _ _ [66,160,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3370

theorem m3620_257 : Upper (D 10) (R 10) [72,96,160,257] 13 :=
  permutation_upper _ _ _ [66,129,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3294

theorem m3620_258 : Upper (D 10) (R 10) [72,96,160,258] 13 :=
  permutation_upper _ _ _ [66,132,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3313

theorem m3620_260 : Upper (D 10) (R 10) [72,96,160,260] 13 :=
  permutation_upper _ _ _ [66,132,288,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3331

theorem m3620_272 : Upper (D 10) (R 10) [72,96,160,272] 13 :=
  permutation_upper _ _ _ [66,144,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3351

theorem m3620_288 : Upper (D 10) (R 10) [72,96,160,288] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3620_384 : Upper (D 10) (R 10) [72,96,160,384] 13 :=
  permutation_upper _ _ _ [66,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3398

def r3620 : Route 9 := (fun mask => (mask,id))

def c3620 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3620 : Upper (D 10) (R 10) [72,96,160] 13 := by
  apply FastRouting.sound _ _ [72,96,160] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,257,258,260,272,288,384] r3620 c3620
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3620_3
  · exact m3620_5
  · exact m3620_6
  · exact m3620_17
  · exact m3620_18
  · exact m3620_20
  · exact m3620_33
  · exact m3620_34
  · exact m3620_36
  · exact m3620_48
  · exact m3620_129
  · exact m3620_130
  · exact m3620_132
  · exact m3620_144
  · exact m3620_160
  · exact m3620_257
  · exact m3620_258
  · exact m3620_260
  · exact m3620_272
  · exact m3620_288
  · exact m3620_384

theorem m3621_3 : Upper (D 10) (R 10) [72,96,384,3] 13 :=
  permutation_upper _ _ _ [6,65,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2628

theorem m3621_5 : Upper (D 10) (R 10) [72,96,384,5] 13 :=
  permutation_upper _ _ _ [6,65,384,96] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2660

theorem m3621_6 : Upper (D 10) (R 10) [72,96,384,6] 13 :=
  permutation_upper _ _ _ [6,96,384,65] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2769

theorem m3621_17 : Upper (D 10) (R 10) [72,96,384,17] 13 :=
  permutation_upper _ _ _ [18,65,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2827

theorem m3621_18 : Upper (D 10) (R 10) [72,96,384,18] 13 :=
  permutation_upper _ _ _ [18,96,65,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2901

theorem m3621_20 : Upper (D 10) (R 10) [72,96,384,20] 13 :=
  permutation_upper _ _ _ [18,192,257,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2955

theorem m3621_33 : Upper (D 10) (R 10) [72,96,384,33] 13 :=
  permutation_upper _ _ _ [34,65,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3018

theorem m3621_34 : Upper (D 10) (R 10) [72,96,384,34] 13 :=
  permutation_upper _ _ _ [34,96,65,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3151

theorem m3621_36 : Upper (D 10) (R 10) [72,96,384,36] 13 :=
  permutation_upper _ _ _ [34,192,257,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3209

theorem m3621_48 : Upper (D 10) (R 10) [72,96,384,48] 13 :=
  permutation_upper _ _ _ [48,65,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3225

theorem m3621_129 : Upper (D 10) (R 10) [72,96,384,129] 13 :=
  permutation_upper _ _ _ [66,129,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3295

theorem m3621_130 : Upper (D 10) (R 10) [72,96,384,130] 13 :=
  permutation_upper _ _ _ [66,132,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3314

theorem m3621_132 : Upper (D 10) (R 10) [72,96,384,132] 13 :=
  permutation_upper _ _ _ [66,132,384,96] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3342

theorem m3621_144 : Upper (D 10) (R 10) [72,96,384,144] 13 :=
  permutation_upper _ _ _ [66,144,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3352

theorem m3621_160 : Upper (D 10) (R 10) [72,96,384,160] 13 :=
  permutation_upper _ _ _ [66,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3374

theorem m3621_384 : Upper (D 10) (R 10) [72,96,384,384] 13 :=
  permutation_upper _ _ _ [66,384,96,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3399

def r3621 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 260 => (132,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3621 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3621 : Upper (D 10) (R 10) [72,96,384] 13 := by
  apply FastRouting.sound _ _ [72,96,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,384] r3621 c3621
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3621_3
  · exact m3621_5
  · exact m3621_6
  · exact m3621_17
  · exact m3621_18
  · exact m3621_20
  · exact m3621_33
  · exact m3621_34
  · exact m3621_36
  · exact m3621_48
  · exact m3621_129
  · exact m3621_130
  · exact m3621_132
  · exact m3621_144
  · exact m3621_160
  · exact m3621_384

theorem m3622_3 : Upper (D 10) (R 10) [72,160,192,3] 13 :=
  permutation_upper _ _ _ [6,65,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2650

theorem m3622_5 : Upper (D 10) (R 10) [72,160,192,5] 13 :=
  permutation_upper _ _ _ [6,65,192,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2655

theorem m3622_6 : Upper (D 10) (R 10) [72,160,192,6] 13 :=
  permutation_upper _ _ _ [6,96,192,129] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2761

theorem m3622_17 : Upper (D 10) (R 10) [72,160,192,17] 13 :=
  permutation_upper _ _ _ [18,65,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2831

theorem m3622_18 : Upper (D 10) (R 10) [72,160,192,18] 13 :=
  permutation_upper _ _ _ [18,96,129,192] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2911

theorem m3622_20 : Upper (D 10) (R 10) [72,160,192,20] 13 :=
  permutation_upper _ _ _ [18,192,65,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2937

theorem m3622_33 : Upper (D 10) (R 10) [72,160,192,33] 13 :=
  permutation_upper _ _ _ [34,65,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3032

theorem m3622_34 : Upper (D 10) (R 10) [72,160,192,34] 13 :=
  permutation_upper _ _ _ [34,96,129,192] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3160

theorem m3622_36 : Upper (D 10) (R 10) [72,160,192,36] 13 :=
  permutation_upper _ _ _ [34,192,65,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3181

theorem m3622_48 : Upper (D 10) (R 10) [72,160,192,48] 13 :=
  permutation_upper _ _ _ [48,65,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3235

theorem m3622_257 : Upper (D 10) (R 10) [72,160,192,257] 13 :=
  permutation_upper _ _ _ [66,129,288,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3301

theorem m3622_258 : Upper (D 10) (R 10) [72,160,192,258] 13 :=
  permutation_upper _ _ _ [66,132,288,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3337

theorem m3622_260 : Upper (D 10) (R 10) [72,160,192,260] 13 :=
  permutation_upper _ _ _ [66,132,320,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3340

theorem m3622_272 : Upper (D 10) (R 10) [72,160,192,272] 13 :=
  permutation_upper _ _ _ [66,144,288,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3360

theorem m3622_288 : Upper (D 10) (R 10) [72,160,192,288] 13 :=
  permutation_upper _ _ _ [66,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3390

def r3622 : Route 9 := (fun mask => (mask,id))

def c3622 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3622 : Upper (D 10) (R 10) [72,160,192] 13 := by
  apply FastRouting.sound _ _ [72,160,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r3622 c3622
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3622_3
  · exact m3622_5
  · exact m3622_6
  · exact m3622_17
  · exact m3622_18
  · exact m3622_20
  · exact m3622_33
  · exact m3622_34
  · exact m3622_36
  · exact m3622_48
  · exact m3622_257
  · exact m3622_258
  · exact m3622_260
  · exact m3622_272
  · exact m3622_288

theorem m3623_3 : Upper (D 10) (R 10) [72,160,288,3] 13 :=
  permutation_upper _ _ _ [6,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2652

theorem m3623_5 : Upper (D 10) (R 10) [72,160,288,5] 13 :=
  permutation_upper _ _ _ [6,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2652

theorem m3623_6 : Upper (D 10) (R 10) [72,160,288,6] 13 :=
  permutation_upper _ _ _ [6,96,160,257] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2755

theorem m3623_17 : Upper (D 10) (R 10) [72,160,288,17] 13 :=
  permutation_upper _ _ _ [18,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2832

theorem m3623_18 : Upper (D 10) (R 10) [72,160,288,18] 13 :=
  permutation_upper _ _ _ [18,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2913

theorem m3623_20 : Upper (D 10) (R 10) [72,160,288,20] 13 :=
  permutation_upper _ _ _ [18,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2913

theorem m3623_33 : Upper (D 10) (R 10) [72,160,288,33] 13 :=
  permutation_upper _ _ _ [34,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3033

theorem m3623_34 : Upper (D 10) (R 10) [72,160,288,34] 13 :=
  permutation_upper _ _ _ [34,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3162

theorem m3623_36 : Upper (D 10) (R 10) [72,160,288,36] 13 :=
  permutation_upper _ _ _ [34,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3162

theorem m3623_48 : Upper (D 10) (R 10) [72,160,288,48] 13 :=
  permutation_upper _ _ _ [48,65,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3236

theorem m3623_65 : Upper (D 10) (R 10) [72,160,288,65] 13 :=
  permutation_upper _ _ _ [66,65,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3257

theorem m3623_66 : Upper (D 10) (R 10) [72,160,288,66] 13 :=
  permutation_upper _ _ _ [66,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3266

theorem m3623_68 : Upper (D 10) (R 10) [72,160,288,68] 13 :=
  permutation_upper _ _ _ [66,68,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3266

theorem m3623_80 : Upper (D 10) (R 10) [72,160,288,80] 13 :=
  permutation_upper _ _ _ [66,80,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3276

theorem m3623_96 : Upper (D 10) (R 10) [72,160,288,96] 13 :=
  permutation_upper _ _ _ [66,96,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3284

theorem m3623_129 : Upper (D 10) (R 10) [72,160,288,129] 13 :=
  permutation_upper _ _ _ [66,129,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3294

theorem m3623_130 : Upper (D 10) (R 10) [72,160,288,130] 13 :=
  permutation_upper _ _ _ [66,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3280

theorem m3623_132 : Upper (D 10) (R 10) [72,160,288,132] 13 :=
  permutation_upper _ _ _ [66,132,288,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3333

theorem m3623_144 : Upper (D 10) (R 10) [72,160,288,144] 13 :=
  permutation_upper _ _ _ [66,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3356

theorem m3623_160 : Upper (D 10) (R 10) [72,160,288,160] 13 :=
  permutation_upper _ _ _ [66,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3379

theorem m3623_192 : Upper (D 10) (R 10) [72,160,288,192] 13 :=
  permutation_upper _ _ _ [66,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3393

theorem m3623_257 : Upper (D 10) (R 10) [72,160,288,257] 13 :=
  permutation_upper _ _ _ [66,129,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3294

theorem m3623_258 : Upper (D 10) (R 10) [72,160,288,258] 13 :=
  permutation_upper _ _ _ [66,132,288,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3333

theorem m3623_260 : Upper (D 10) (R 10) [72,160,288,260] 13 :=
  permutation_upper _ _ _ [66,96,129,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3280

theorem m3623_272 : Upper (D 10) (R 10) [72,160,288,272] 13 :=
  permutation_upper _ _ _ [66,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3356

theorem m3623_288 : Upper (D 10) (R 10) [72,160,288,288] 13 :=
  permutation_upper _ _ _ [66,160,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3379

theorem m3623_320 : Upper (D 10) (R 10) [72,160,288,320] 13 :=
  permutation_upper _ _ _ [66,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3393

theorem m3623_384 : Upper (D 10) (R 10) [72,160,288,384] 13 :=
  permutation_upper _ _ _ [66,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3403

def r3623 : Route 9 := (fun mask => (mask,id))

def c3623 : Nat → Fin 9 := (fun _ => 0)

theorem u3623 : Upper (D 10) (R 10) [72,160,288] 13 := by
  apply FastRouting.sound _ _ [72,160,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,129,130,132,144,160,192,257,258,260,272,288,320,384] r3623 c3623
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3623_3
  · exact m3623_5
  · exact m3623_6
  · exact m3623_17
  · exact m3623_18
  · exact m3623_20
  · exact m3623_33
  · exact m3623_34
  · exact m3623_36
  · exact m3623_48
  · exact m3623_65
  · exact m3623_66
  · exact m3623_68
  · exact m3623_80
  · exact m3623_96
  · exact m3623_129
  · exact m3623_130
  · exact m3623_132
  · exact m3623_144
  · exact m3623_160
  · exact m3623_192
  · exact m3623_257
  · exact m3623_258
  · exact m3623_260
  · exact m3623_272
  · exact m3623_288
  · exact m3623_320
  · exact m3623_384

theorem m3624_3 : Upper (D 10) (R 10) [72,160,320,3] 13 :=
  permutation_upper _ _ _ [6,65,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2653

theorem m3624_5 : Upper (D 10) (R 10) [72,160,320,5] 13 :=
  permutation_upper _ _ _ [6,65,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2656

theorem m3624_6 : Upper (D 10) (R 10) [72,160,320,6] 13 :=
  permutation_upper _ _ _ [6,96,384,129] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2772

theorem m3624_17 : Upper (D 10) (R 10) [72,160,320,17] 13 :=
  permutation_upper _ _ _ [18,65,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2833

theorem m3624_18 : Upper (D 10) (R 10) [72,160,320,18] 13 :=
  permutation_upper _ _ _ [18,96,129,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2915

theorem m3624_20 : Upper (D 10) (R 10) [72,160,320,20] 13 :=
  permutation_upper _ _ _ [18,192,65,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2939

theorem m3624_33 : Upper (D 10) (R 10) [72,160,320,33] 13 :=
  permutation_upper _ _ _ [34,65,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3034

theorem m3624_34 : Upper (D 10) (R 10) [72,160,320,34] 13 :=
  permutation_upper _ _ _ [34,96,129,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3164

theorem m3624_36 : Upper (D 10) (R 10) [72,160,320,36] 13 :=
  permutation_upper _ _ _ [34,192,65,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3183

theorem m3624_48 : Upper (D 10) (R 10) [72,160,320,48] 13 :=
  permutation_upper _ _ _ [48,65,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3237

theorem m3624_129 : Upper (D 10) (R 10) [72,160,320,129] 13 :=
  permutation_upper _ _ _ [66,129,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3295

theorem m3624_130 : Upper (D 10) (R 10) [72,160,320,130] 13 :=
  permutation_upper _ _ _ [66,96,129,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3281

theorem m3624_132 : Upper (D 10) (R 10) [72,160,320,132] 13 :=
  permutation_upper _ _ _ [66,132,320,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3339

theorem m3624_144 : Upper (D 10) (R 10) [72,160,320,144] 13 :=
  permutation_upper _ _ _ [66,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3357

theorem m3624_160 : Upper (D 10) (R 10) [72,160,320,160] 13 :=
  permutation_upper _ _ _ [66,160,160,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3380

theorem m3624_257 : Upper (D 10) (R 10) [72,160,320,257] 13 :=
  permutation_upper _ _ _ [66,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3297

theorem m3624_258 : Upper (D 10) (R 10) [72,160,320,258] 13 :=
  permutation_upper _ _ _ [66,132,288,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3334

theorem m3624_260 : Upper (D 10) (R 10) [72,160,320,260] 13 :=
  permutation_upper _ _ _ [66,132,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3316

theorem m3624_272 : Upper (D 10) (R 10) [72,160,320,272] 13 :=
  permutation_upper _ _ _ [66,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3359

theorem m3624_288 : Upper (D 10) (R 10) [72,160,320,288] 13 :=
  permutation_upper _ _ _ [66,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3383

theorem m3624_384 : Upper (D 10) (R 10) [72,160,320,384] 13 :=
  permutation_upper _ _ _ [66,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3404

def r3624 : Route 9 := (fun mask => (mask,id))

def c3624 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3624 : Upper (D 10) (R 10) [72,160,320] 13 := by
  apply FastRouting.sound _ _ [72,160,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,257,258,260,272,288,384] r3624 c3624
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3624_3
  · exact m3624_5
  · exact m3624_6
  · exact m3624_17
  · exact m3624_18
  · exact m3624_20
  · exact m3624_33
  · exact m3624_34
  · exact m3624_36
  · exact m3624_48
  · exact m3624_129
  · exact m3624_130
  · exact m3624_132
  · exact m3624_144
  · exact m3624_160
  · exact m3624_257
  · exact m3624_258
  · exact m3624_260
  · exact m3624_272
  · exact m3624_288
  · exact m3624_384

theorem m3625_3 : Upper (D 10) (R 10) [72,160,384,3] 13 :=
  permutation_upper _ _ _ [6,65,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2654

theorem m3625_5 : Upper (D 10) (R 10) [72,160,384,5] 13 :=
  permutation_upper _ _ _ [6,65,384,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2662

theorem m3625_6 : Upper (D 10) (R 10) [72,160,384,6] 13 :=
  permutation_upper _ _ _ [6,96,192,257] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2763

theorem m3625_17 : Upper (D 10) (R 10) [72,160,384,17] 13 :=
  permutation_upper _ _ _ [18,65,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2834

theorem m3625_18 : Upper (D 10) (R 10) [72,160,384,18] 13 :=
  permutation_upper _ _ _ [18,96,129,320] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2914

theorem m3625_20 : Upper (D 10) (R 10) [72,160,384,20] 13 :=
  permutation_upper _ _ _ [18,192,96,257] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2948

theorem m3625_33 : Upper (D 10) (R 10) [72,160,384,33] 13 :=
  permutation_upper _ _ _ [34,65,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3035

theorem m3625_34 : Upper (D 10) (R 10) [72,160,384,34] 13 :=
  permutation_upper _ _ _ [34,96,129,320] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3163

theorem m3625_36 : Upper (D 10) (R 10) [72,160,384,36] 13 :=
  permutation_upper _ _ _ [34,192,96,257] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3199

theorem m3625_48 : Upper (D 10) (R 10) [72,160,384,48] 13 :=
  permutation_upper _ _ _ [48,65,160,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3238

theorem m3625_65 : Upper (D 10) (R 10) [72,160,384,65] 13 :=
  permutation_upper _ _ _ [66,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3258

theorem m3625_66 : Upper (D 10) (R 10) [72,160,384,66] 13 :=
  permutation_upper _ _ _ [66,68,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3267

theorem m3625_68 : Upper (D 10) (R 10) [72,160,384,68] 13 :=
  permutation_upper _ _ _ [66,68,384,160] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3269

theorem m3625_80 : Upper (D 10) (R 10) [72,160,384,80] 13 :=
  permutation_upper _ _ _ [66,80,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3277

theorem m3625_96 : Upper (D 10) (R 10) [72,160,384,96] 13 :=
  permutation_upper _ _ _ [66,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3285

theorem m3625_257 : Upper (D 10) (R 10) [72,160,384,257] 13 :=
  permutation_upper _ _ _ [66,129,288,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3301

theorem m3625_258 : Upper (D 10) (R 10) [72,160,384,258] 13 :=
  permutation_upper _ _ _ [66,132,288,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3338

theorem m3625_260 : Upper (D 10) (R 10) [72,160,384,260] 13 :=
  permutation_upper _ _ _ [66,132,384,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3343

theorem m3625_272 : Upper (D 10) (R 10) [72,160,384,272] 13 :=
  permutation_upper _ _ _ [66,144,288,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3361

theorem m3625_288 : Upper (D 10) (R 10) [72,160,384,288] 13 :=
  permutation_upper _ _ _ [66,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3391

theorem m3625_320 : Upper (D 10) (R 10) [72,160,384,320] 13 :=
  permutation_upper _ _ _ [66,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3394

def r3625 : Route 9 := (fun mask => (mask,id))

def c3625 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 130 => 7 | 132 => 7 | 144 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3625 : Upper (D 10) (R 10) [72,160,384] 13 := by
  apply FastRouting.sound _ _ [72,160,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,65,66,68,80,96,257,258,260,272,288,320] r3625 c3625
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3625_3
  · exact m3625_5
  · exact m3625_6
  · exact m3625_17
  · exact m3625_18
  · exact m3625_20
  · exact m3625_33
  · exact m3625_34
  · exact m3625_36
  · exact m3625_48
  · exact m3625_65
  · exact m3625_66
  · exact m3625_68
  · exact m3625_80
  · exact m3625_96
  · exact m3625_257
  · exact m3625_258
  · exact m3625_260
  · exact m3625_272
  · exact m3625_288
  · exact m3625_320

theorem m3626_3 : Upper (D 10) (R 10) [72,192,384,3] 13 :=
  permutation_upper _ _ _ [6,65,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2657

theorem m3626_5 : Upper (D 10) (R 10) [72,192,384,5] 13 :=
  permutation_upper _ _ _ [6,65,384,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2663

theorem m3626_6 : Upper (D 10) (R 10) [72,192,384,6] 13 :=
  permutation_upper _ _ _ [6,192,320,129] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2782

theorem m3626_17 : Upper (D 10) (R 10) [72,192,384,17] 13 :=
  permutation_upper _ _ _ [18,65,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2835

theorem m3626_18 : Upper (D 10) (R 10) [72,192,384,18] 13 :=
  permutation_upper _ _ _ [18,192,65,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2940

theorem m3626_20 : Upper (D 10) (R 10) [72,192,384,20] 13 :=
  permutation_upper _ _ _ [18,192,257,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2956

theorem m3626_33 : Upper (D 10) (R 10) [72,192,384,33] 13 :=
  permutation_upper _ _ _ [34,65,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3036

theorem m3626_34 : Upper (D 10) (R 10) [72,192,384,34] 13 :=
  permutation_upper _ _ _ [34,192,65,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3184

theorem m3626_36 : Upper (D 10) (R 10) [72,192,384,36] 13 :=
  permutation_upper _ _ _ [34,192,257,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3210

theorem m3626_48 : Upper (D 10) (R 10) [72,192,384,48] 13 :=
  permutation_upper _ _ _ [48,65,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3239

theorem m3626_257 : Upper (D 10) (R 10) [72,192,384,257] 13 :=
  permutation_upper _ _ _ [66,129,320,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3302

theorem m3626_258 : Upper (D 10) (R 10) [72,192,384,258] 13 :=
  permutation_upper _ _ _ [66,132,320,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3341

theorem m3626_260 : Upper (D 10) (R 10) [72,192,384,260] 13 :=
  permutation_upper _ _ _ [66,132,384,320] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3344

theorem m3626_272 : Upper (D 10) (R 10) [72,192,384,272] 13 :=
  permutation_upper _ _ _ [66,144,320,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3362

theorem m3626_288 : Upper (D 10) (R 10) [72,192,384,288] 13 :=
  permutation_upper _ _ _ [66,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3392

def r3626 : Route 9 := (fun mask => (mask,id))

def c3626 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3626 : Upper (D 10) (R 10) [72,192,384] 13 := by
  apply FastRouting.sound _ _ [72,192,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r3626 c3626
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3626_3
  · exact m3626_5
  · exact m3626_6
  · exact m3626_17
  · exact m3626_18
  · exact m3626_20
  · exact m3626_33
  · exact m3626_34
  · exact m3626_36
  · exact m3626_48
  · exact m3626_257
  · exact m3626_258
  · exact m3626_260
  · exact m3626_272
  · exact m3626_288

def b3627 : PairBound 9 := { available := 415, camps := [{ cop := 0, region := 2, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 97 98 164 415 415 447 479 415 415), lower := (rows 97 98 164 8 16 32 64 128 256), losses := [] }

theorem u3627 : Upper (D 10) (R 10) [96,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3627 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3628 : PairBound 9 := { available := 447, camps := [{ cop := 0, region := 2, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 97 98 388 447 447 447 511 447 447), lower := (rows 97 98 388 8 16 32 64 128 256), losses := [] }

theorem u3628 : Upper (D 10) (R 10) [96,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3628 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3629_3 : Upper (D 10) (R 10) [96,160,192,3] 13 :=
  permutation_upper _ _ _ [6,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2754

theorem m3629_5 : Upper (D 10) (R 10) [96,160,192,5] 13 :=
  permutation_upper _ _ _ [6,96,192,160] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2762

theorem m3629_6 : Upper (D 10) (R 10) [96,160,192,6] 13 :=
  permutation_upper _ _ _ [6,96,192,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2762

theorem m3629_17 : Upper (D 10) (R 10) [96,160,192,17] 13 :=
  permutation_upper _ _ _ [18,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2919

theorem m3629_18 : Upper (D 10) (R 10) [96,160,192,18] 13 :=
  permutation_upper _ _ _ [18,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2919

theorem m3629_20 : Upper (D 10) (R 10) [96,160,192,20] 13 :=
  permutation_upper _ _ _ [18,192,96,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2947

theorem m3629_33 : Upper (D 10) (R 10) [96,160,192,33] 13 :=
  permutation_upper _ _ _ [34,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3168

theorem m3629_34 : Upper (D 10) (R 10) [96,160,192,34] 13 :=
  permutation_upper _ _ _ [34,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3168

theorem m3629_36 : Upper (D 10) (R 10) [96,160,192,36] 13 :=
  permutation_upper _ _ _ [34,192,96,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3198

theorem m3629_48 : Upper (D 10) (R 10) [96,160,192,48] 13 :=
  permutation_upper _ _ _ [48,96,160,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3251

theorem m3629_257 : Upper (D 10) (R 10) [96,160,192,257] 13 :=
  permutation_upper _ _ _ [66,160,288,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3391

theorem m3629_258 : Upper (D 10) (R 10) [96,160,192,258] 13 :=
  permutation_upper _ _ _ [66,160,288,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3391

theorem m3629_260 : Upper (D 10) (R 10) [96,160,192,260] 13 :=
  permutation_upper _ _ _ [66,384,160,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3403

theorem m3629_272 : Upper (D 10) (R 10) [96,160,192,272] 13 :=
  permutation_upper _ _ _ [80,160,288,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3408

def r3629 : Route 9 := (fun mask => (mask,id))

def c3629 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3629 : Upper (D 10) (R 10) [96,160,192] 13 := by
  apply FastRouting.sound _ _ [96,160,192] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r3629 c3629
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3629_3
  · exact m3629_5
  · exact m3629_6
  · exact m3629_17
  · exact m3629_18
  · exact m3629_20
  · exact m3629_33
  · exact m3629_34
  · exact m3629_36
  · exact m3629_48
  · exact m3629_257
  · exact m3629_258
  · exact m3629_260
  · exact m3629_272
  · exact u3411

theorem m3630_3 : Upper (D 10) (R 10) [96,160,288,3] 13 :=
  permutation_upper _ _ _ [6,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2757

theorem m3630_5 : Upper (D 10) (R 10) [96,160,288,5] 13 :=
  permutation_upper _ _ _ [6,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2757

theorem m3630_6 : Upper (D 10) (R 10) [96,160,288,6] 13 :=
  permutation_upper _ _ _ [6,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2757

theorem m3630_17 : Upper (D 10) (R 10) [96,160,288,17] 13 :=
  permutation_upper _ _ _ [18,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2920

theorem m3630_18 : Upper (D 10) (R 10) [96,160,288,18] 13 :=
  permutation_upper _ _ _ [18,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2920

theorem m3630_20 : Upper (D 10) (R 10) [96,160,288,20] 13 :=
  permutation_upper _ _ _ [18,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2920

theorem m3630_65 : Upper (D 10) (R 10) [96,160,288,65] 13 :=
  permutation_upper _ _ _ [66,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3284

theorem m3630_66 : Upper (D 10) (R 10) [96,160,288,66] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_68 : Upper (D 10) (R 10) [96,160,288,68] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_80 : Upper (D 10) (R 10) [96,160,288,80] 13 :=
  permutation_upper _ _ _ [80,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3405

theorem m3630_129 : Upper (D 10) (R 10) [96,160,288,129] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_130 : Upper (D 10) (R 10) [96,160,288,130] 13 :=
  permutation_upper _ _ _ [66,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3284

theorem m3630_132 : Upper (D 10) (R 10) [96,160,288,132] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_144 : Upper (D 10) (R 10) [96,160,288,144] 13 :=
  permutation_upper _ _ _ [80,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3405

theorem m3630_192 : Upper (D 10) (R 10) [96,160,288,192] 13 :=
  permutation_upper _ _ _ [96,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3411

theorem m3630_257 : Upper (D 10) (R 10) [96,160,288,257] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_258 : Upper (D 10) (R 10) [96,160,288,258] 13 :=
  permutation_upper _ _ _ [66,160,96,288] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

theorem m3630_260 : Upper (D 10) (R 10) [96,160,288,260] 13 :=
  permutation_upper _ _ _ [66,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3284

theorem m3630_272 : Upper (D 10) (R 10) [96,160,288,272] 13 :=
  permutation_upper _ _ _ [80,96,160,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3405

theorem m3630_320 : Upper (D 10) (R 10) [96,160,288,320] 13 :=
  permutation_upper _ _ _ [96,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3411

theorem m3630_384 : Upper (D 10) (R 10) [96,160,288,384] 13 :=
  permutation_upper _ _ _ [96,160,192,288] (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3411

def r3630 : Route 9 := (fun mask => (mask,id))

def c3630 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 34 => 5 | 36 => 5 | 48 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3630 : Upper (D 10) (R 10) [96,160,288] 13 := by
  apply FastRouting.sound _ _ [96,160,288] 13 (by decide) (choices 2) [3,5,6,17,18,20,65,66,68,80,129,130,132,144,192,257,258,260,272,320,384] r3630 c3630
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3630_3
  · exact m3630_5
  · exact m3630_6
  · exact m3630_17
  · exact m3630_18
  · exact m3630_20
  · exact m3630_65
  · exact m3630_66
  · exact m3630_68
  · exact m3630_80
  · exact m3630_129
  · exact m3630_130
  · exact m3630_132
  · exact m3630_144
  · exact m3630_192
  · exact m3630_257
  · exact m3630_258
  · exact m3630_260
  · exact m3630_272
  · exact m3630_320
  · exact m3630_384

theorem m3631_3 : Upper (D 10) (R 10) [96,160,320,3] 13 :=
  permutation_upper _ _ _ [6,96,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2758

theorem m3631_5 : Upper (D 10) (R 10) [96,160,320,5] 13 :=
  permutation_upper _ _ _ [6,96,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2764

theorem m3631_6 : Upper (D 10) (R 10) [96,160,320,6] 13 :=
  permutation_upper _ _ _ [6,96,384,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2774

theorem m3631_17 : Upper (D 10) (R 10) [96,160,320,17] 13 :=
  permutation_upper _ _ _ [18,96,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2921

theorem m3631_18 : Upper (D 10) (R 10) [96,160,320,18] 13 :=
  permutation_upper _ _ _ [18,96,160,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2922

theorem m3631_20 : Upper (D 10) (R 10) [96,160,320,20] 13 :=
  permutation_upper _ _ _ [18,192,96,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2950

theorem m3631_33 : Upper (D 10) (R 10) [96,160,320,33] 13 :=
  permutation_upper _ _ _ [34,96,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3169

theorem m3631_34 : Upper (D 10) (R 10) [96,160,320,34] 13 :=
  permutation_upper _ _ _ [34,96,160,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3170

theorem m3631_36 : Upper (D 10) (R 10) [96,160,320,36] 13 :=
  permutation_upper _ _ _ [34,192,96,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3202

theorem m3631_48 : Upper (D 10) (R 10) [96,160,320,48] 13 :=
  permutation_upper _ _ _ [48,96,160,320] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3252

theorem m3631_129 : Upper (D 10) (R 10) [96,160,320,129] 13 :=
  permutation_upper _ _ _ [66,160,96,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3374

theorem m3631_130 : Upper (D 10) (R 10) [96,160,320,130] 13 :=
  permutation_upper _ _ _ [66,96,160,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3285

theorem m3631_132 : Upper (D 10) (R 10) [96,160,320,132] 13 :=
  permutation_upper _ _ _ [66,384,96,160] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3398

theorem m3631_144 : Upper (D 10) (R 10) [96,160,320,144] 13 :=
  permutation_upper _ _ _ [80,96,160,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3406

theorem m3631_160 : Upper (D 10) (R 10) [96,160,320,160] 13 :=
  permutation_upper _ _ _ [96,96,160,384] (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3410

theorem m3631_257 : Upper (D 10) (R 10) [96,160,320,257] 13 :=
  permutation_upper _ _ _ [66,160,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3383

theorem m3631_258 : Upper (D 10) (R 10) [96,160,320,258] 13 :=
  permutation_upper _ _ _ [66,160,288,320] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3390

theorem m3631_260 : Upper (D 10) (R 10) [96,160,320,260] 13 :=
  permutation_upper _ _ _ [66,192,160,288] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3393

theorem m3631_272 : Upper (D 10) (R 10) [96,160,320,272] 13 :=
  permutation_upper _ _ _ [80,160,192,288] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3407

theorem m3631_288 : Upper (D 10) (R 10) [96,160,320,288] 13 :=
  permutation_upper _ _ _ [96,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3411

def r3631 : Route 9 := (fun mask => (mask,id))

def c3631 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3631 : Upper (D 10) (R 10) [96,160,320] 13 := by
  apply FastRouting.sound _ _ [96,160,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,129,130,132,144,160,257,258,260,272,288,384] r3631 c3631
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3631_3
  · exact m3631_5
  · exact m3631_6
  · exact m3631_17
  · exact m3631_18
  · exact m3631_20
  · exact m3631_33
  · exact m3631_34
  · exact m3631_36
  · exact m3631_48
  · exact m3631_129
  · exact m3631_130
  · exact m3631_132
  · exact m3631_144
  · exact m3631_160
  · exact m3631_257
  · exact m3631_258
  · exact m3631_260
  · exact m3631_272
  · exact m3631_288
  · exact u3412

theorem m3632_3 : Upper (D 10) (R 10) [96,192,384,3] 13 :=
  permutation_upper _ _ _ [6,96,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2765

theorem m3632_5 : Upper (D 10) (R 10) [96,192,384,5] 13 :=
  permutation_upper _ _ _ [6,96,384,192] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2775

theorem m3632_6 : Upper (D 10) (R 10) [96,192,384,6] 13 :=
  permutation_upper _ _ _ [6,192,320,160] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2783

theorem m3632_17 : Upper (D 10) (R 10) [96,192,384,17] 13 :=
  permutation_upper _ _ _ [18,96,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2923

theorem m3632_18 : Upper (D 10) (R 10) [96,192,384,18] 13 :=
  permutation_upper _ _ _ [18,192,96,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2951

theorem m3632_20 : Upper (D 10) (R 10) [96,192,384,20] 13 :=
  permutation_upper _ _ _ [18,192,288,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2957

theorem m3632_33 : Upper (D 10) (R 10) [96,192,384,33] 13 :=
  permutation_upper _ _ _ [34,96,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3171

theorem m3632_34 : Upper (D 10) (R 10) [96,192,384,34] 13 :=
  permutation_upper _ _ _ [34,192,96,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3203

theorem m3632_36 : Upper (D 10) (R 10) [96,192,384,36] 13 :=
  permutation_upper _ _ _ [34,192,288,320] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3218

theorem m3632_48 : Upper (D 10) (R 10) [96,192,384,48] 13 :=
  permutation_upper _ _ _ [48,96,192,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3253

theorem m3632_257 : Upper (D 10) (R 10) [96,192,384,257] 13 :=
  permutation_upper _ _ _ [66,160,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3392

theorem m3632_258 : Upper (D 10) (R 10) [96,192,384,258] 13 :=
  permutation_upper _ _ _ [66,384,160,320] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3404

theorem m3632_260 : Upper (D 10) (R 10) [96,192,384,260] 13 :=
  permutation_upper _ _ _ [66,192,288,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3394

theorem m3632_272 : Upper (D 10) (R 10) [96,192,384,272] 13 :=
  permutation_upper _ _ _ [80,160,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3409

theorem m3632_288 : Upper (D 10) (R 10) [96,192,384,288] 13 :=
  permutation_upper _ _ _ [96,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3412

def r3632 : Route 9 := (fun mask => (mask,id))

def c3632 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 80 => 6 | 144 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3632 : Upper (D 10) (R 10) [96,192,384] 13 := by
  apply FastRouting.sound _ _ [96,192,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48,257,258,260,272,288] r3632 c3632
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3632_3
  · exact m3632_5
  · exact m3632_6
  · exact m3632_17
  · exact m3632_18
  · exact m3632_20
  · exact m3632_33
  · exact m3632_34
  · exact m3632_36
  · exact m3632_48
  · exact m3632_257
  · exact m3632_258
  · exact m3632_260
  · exact m3632_272
  · exact m3632_288

def b3633 : PairBound 9 := { available := 127, camps := [{ cop := 1, region := 4, targets := 96 }], pairs := [(2,5),(2,6)], upper := (rows 97 386 388 127 127 127 127 255 383), lower := (rows 97 386 388 8 16 32 64 128 256), losses := [] }

theorem u3633 : Upper (D 10) (R 10) [96,384,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3633 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3634_3 : Upper (D 10) (R 10) [192,320,384,3] 13 :=
  permutation_upper _ _ _ [6,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2784

theorem m3634_5 : Upper (D 10) (R 10) [192,320,384,5] 13 :=
  permutation_upper _ _ _ [6,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2784

theorem m3634_6 : Upper (D 10) (R 10) [192,320,384,6] 13 :=
  permutation_upper _ _ _ [6,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2784

theorem m3634_17 : Upper (D 10) (R 10) [192,320,384,17] 13 :=
  permutation_upper _ _ _ [18,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2958

theorem m3634_18 : Upper (D 10) (R 10) [192,320,384,18] 13 :=
  permutation_upper _ _ _ [18,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2958

theorem m3634_20 : Upper (D 10) (R 10) [192,320,384,20] 13 :=
  permutation_upper _ _ _ [18,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2958

theorem m3634_33 : Upper (D 10) (R 10) [192,320,384,33] 13 :=
  permutation_upper _ _ _ [34,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3219

theorem m3634_34 : Upper (D 10) (R 10) [192,320,384,34] 13 :=
  permutation_upper _ _ _ [34,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3219

theorem m3634_36 : Upper (D 10) (R 10) [192,320,384,36] 13 :=
  permutation_upper _ _ _ [34,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3219

theorem m3634_48 : Upper (D 10) (R 10) [192,320,384,48] 13 :=
  permutation_upper _ _ _ [48,192,320,384] (fun i => match i.val with | 0 => 3 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3254

def r3634 : Route 9 := (fun mask => (mask,id))

def c3634 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 80 => 6 | 144 => 7 | 272 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3634 : Upper (D 10) (R 10) [192,320,384] 13 := by
  apply FastRouting.sound _ _ [192,320,384] 13 (by decide) (choices 2) [3,5,6,17,18,20,33,34,36,48] r3634 c3634
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3634_3
  · exact m3634_5
  · exact m3634_6
  · exact m3634_17
  · exact m3634_18
  · exact m3634_20
  · exact m3634_33
  · exact m3634_34
  · exact m3634_36
  · exact m3634_48

def r3635 : Route 9 := (fun mask => match mask with | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3635 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3635 : Upper (D 10) (R 10) [6,9] 13 := by
  apply FastRouting.sound _ _ [6,9] 13 (by decide) (choices 2) [48,80,96,192] r3635 c3635
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3413
  · exact u3414
  · exact u3415
  · exact u3416

def r3636 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3636 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 17 => 4 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u3636 : Upper (D 10) (R 10) [6,24] 13 := by
  apply FastRouting.sound _ _ [6,24] 13 (by decide) (choices 2) [33,65,96,192] r3636 c3636
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u3417
  · exact u3418
  · exact u3419
  · exact u3420

theorem m3637_24 : Upper (D 10) (R 10) [6,33,24] 13 :=
  permutation_upper _ _ _ [6,24,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3417

def r3637 : Route 9 := (fun mask => match mask with | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 264 => (72,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3637 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3637 : Upper (D 10) (R 10) [6,33] 13 := by
  apply FastRouting.sound _ _ [6,33] 13 (by decide) (choices 2) [24,40,72,96,192] r3637 c3637
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact m3637_24
  · exact u3421
  · exact u3422
  · exact u3423
  · exact u3424

theorem m3638_17 : Upper (D 10) (R 10) [6,40,17] 13 :=
  permutation_upper _ _ _ [6,9,48] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3413

theorem m3638_33 : Upper (D 10) (R 10) [6,40,33] 13 :=
  permutation_upper _ _ _ [6,33,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3421

def r3638 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 257 => (65,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3638 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3638 : Upper (D 10) (R 10) [6,40] 13 := by
  apply FastRouting.sound _ _ [6,40] 13 (by decide) (choices 2) [17,33,48,65,80,96,192] r3638 c3638
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3638_17
  · exact m3638_33
  · exact u3425
  · exact u3426
  · exact u3427
  · exact u3428
  · exact u3429

theorem m3639_24 : Upper (D 10) (R 10) [6,65,24] 13 :=
  permutation_upper _ _ _ [6,24,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3418

theorem m3639_40 : Upper (D 10) (R 10) [6,65,40] 13 :=
  permutation_upper _ _ _ [6,40,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3426

def r3639 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3639 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3639 : Upper (D 10) (R 10) [6,65] 13 := by
  apply FastRouting.sound _ _ [6,65] 13 (by decide) (choices 2) [24,40,72,96,136,160,192,384] r3639 c3639
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3639_24
  · exact m3639_40
  · exact u3430
  · exact u3431
  · exact u3432
  · exact u3433
  · exact u3434
  · exact u3435

theorem m3640_17 : Upper (D 10) (R 10) [6,72,17] 13 :=
  permutation_upper _ _ _ [6,9,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3414

theorem m3640_33 : Upper (D 10) (R 10) [6,72,33] 13 :=
  permutation_upper _ _ _ [6,33,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3422

theorem m3640_48 : Upper (D 10) (R 10) [6,72,48] 13 :=
  permutation_upper _ _ _ [6,40,80] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3427

theorem m3640_65 : Upper (D 10) (R 10) [6,72,65] 13 :=
  permutation_upper _ _ _ [6,65,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3430

theorem m3640_129 : Upper (D 10) (R 10) [6,72,129] 13 :=
  permutation_upper _ _ _ [6,65,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3432

def r3640 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3640 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3640 : Upper (D 10) (R 10) [6,72] 13 := by
  apply FastRouting.sound _ _ [6,72] 13 (by decide) (choices 2) [17,33,48,65,80,96,129,144,160,192,384] r3640 c3640
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3640_17
  · exact m3640_33
  · exact m3640_48
  · exact m3640_65
  · exact u3436
  · exact u3437
  · exact m3640_129
  · exact u3438
  · exact u3439
  · exact u3440
  · exact u3441

theorem m3641_9 : Upper (D 10) (R 10) [6,96,9] 13 :=
  permutation_upper _ _ _ [6,9,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3415

theorem m3641_24 : Upper (D 10) (R 10) [6,96,24] 13 :=
  permutation_upper _ _ _ [6,24,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3419

theorem m3641_33 : Upper (D 10) (R 10) [6,96,33] 13 :=
  permutation_upper _ _ _ [6,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3423

theorem m3641_40 : Upper (D 10) (R 10) [6,96,40] 13 :=
  permutation_upper _ _ _ [6,40,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3428

theorem m3641_65 : Upper (D 10) (R 10) [6,96,65] 13 :=
  permutation_upper _ _ _ [6,65,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3431

theorem m3641_72 : Upper (D 10) (R 10) [6,96,72] 13 :=
  permutation_upper _ _ _ [6,72,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3437

theorem m3641_129 : Upper (D 10) (R 10) [6,96,129] 13 :=
  permutation_upper _ _ _ [6,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3433

theorem m3641_136 : Upper (D 10) (R 10) [6,96,136] 13 :=
  permutation_upper _ _ _ [6,72,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3439

def r3641 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3641 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3641 : Upper (D 10) (R 10) [6,96] 13 := by
  apply FastRouting.sound _ _ [6,96] 13 (by decide) (choices 2) [9,24,33,40,65,72,96,129,136,160,192,384] r3641 c3641
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3641_9
  · exact m3641_24
  · exact m3641_33
  · exact m3641_40
  · exact m3641_65
  · exact m3641_72
  · exact u3442
  · exact m3641_129
  · exact m3641_136
  · exact u3443
  · exact u3444
  · exact u3445

theorem m3642_9 : Upper (D 10) (R 10) [6,192,9] 13 :=
  permutation_upper _ _ _ [6,9,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3416

theorem m3642_24 : Upper (D 10) (R 10) [6,192,24] 13 :=
  permutation_upper _ _ _ [6,24,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3420

theorem m3642_33 : Upper (D 10) (R 10) [6,192,33] 13 :=
  permutation_upper _ _ _ [6,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3424

theorem m3642_40 : Upper (D 10) (R 10) [6,192,40] 13 :=
  permutation_upper _ _ _ [6,40,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3429

theorem m3642_65 : Upper (D 10) (R 10) [6,192,65] 13 :=
  permutation_upper _ _ _ [6,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3434

theorem m3642_72 : Upper (D 10) (R 10) [6,192,72] 13 :=
  permutation_upper _ _ _ [6,72,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3440

theorem m3642_96 : Upper (D 10) (R 10) [6,192,96] 13 :=
  permutation_upper _ _ _ [6,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3444

theorem m3642_257 : Upper (D 10) (R 10) [6,192,257] 13 :=
  permutation_upper _ _ _ [6,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3435

theorem m3642_264 : Upper (D 10) (R 10) [6,192,264] 13 :=
  permutation_upper _ _ _ [6,72,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3441

theorem m3642_288 : Upper (D 10) (R 10) [6,192,288] 13 :=
  permutation_upper _ _ _ [6,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3445

def r3642 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3642 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3642 : Upper (D 10) (R 10) [6,192] 13 := by
  apply FastRouting.sound _ _ [6,192] 13 (by decide) (choices 2) [9,24,33,40,65,72,96,192,257,264,288,320] r3642 c3642
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3642_9
  · exact m3642_24
  · exact m3642_33
  · exact m3642_40
  · exact m3642_65
  · exact m3642_72
  · exact m3642_96
  · exact u3446
  · exact m3642_257
  · exact m3642_264
  · exact m3642_288
  · exact u3447

theorem m3643_18 : Upper (D 10) (R 10) [12,33,18] 13 :=
  permutation_upper _ _ _ [10,20,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3450

theorem m3643_34 : Upper (D 10) (R 10) [12,33,34] 13 :=
  permutation_upper _ _ _ [10,36,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3456

theorem m3643_48 : Upper (D 10) (R 10) [12,33,48] 13 :=
  permutation_upper _ _ _ [10,48,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3460

theorem m3643_66 : Upper (D 10) (R 10) [12,33,66] 13 :=
  permutation_upper _ _ _ [10,68,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3468

theorem m3643_80 : Upper (D 10) (R 10) [12,33,80] 13 :=
  permutation_upper _ _ _ [10,80,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3475

theorem m3643_96 : Upper (D 10) (R 10) [12,33,96] 13 :=
  permutation_upper _ _ _ [10,96,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3482

theorem m3643_192 : Upper (D 10) (R 10) [12,33,192] 13 :=
  permutation_upper _ _ _ [10,192,33] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3489

def r3643 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 258 => (66,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 272 => (80,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 288 => (96,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 384 => (192,(fun i => match i.val with | 6 => 8 | 8 => 6 | _ => i)) | _ => (mask,id))

def c3643 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3643 : Upper (D 10) (R 10) [12,33] 13 := by
  apply FastRouting.sound _ _ [12,33] 13 (by decide) (choices 2) [18,34,48,66,80,96,192] r3643 c3643
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3643_18
  · exact m3643_34
  · exact m3643_48
  · exact m3643_66
  · exact m3643_80
  · exact m3643_96
  · exact m3643_192

theorem m3644_18 : Upper (D 10) (R 10) [12,65,18] 13 :=
  permutation_upper _ _ _ [10,20,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3451

theorem m3644_34 : Upper (D 10) (R 10) [12,65,34] 13 :=
  permutation_upper _ _ _ [10,36,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3457

theorem m3644_48 : Upper (D 10) (R 10) [12,65,48] 13 :=
  permutation_upper _ _ _ [10,48,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3461

theorem m3644_66 : Upper (D 10) (R 10) [12,65,66] 13 :=
  permutation_upper _ _ _ [10,68,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3469

theorem m3644_80 : Upper (D 10) (R 10) [12,65,80] 13 :=
  permutation_upper _ _ _ [10,80,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3476

theorem m3644_96 : Upper (D 10) (R 10) [12,65,96] 13 :=
  permutation_upper _ _ _ [10,96,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3483

theorem m3644_130 : Upper (D 10) (R 10) [12,65,130] 13 :=
  permutation_upper _ _ _ [10,68,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3471

theorem m3644_144 : Upper (D 10) (R 10) [12,65,144] 13 :=
  permutation_upper _ _ _ [10,80,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3478

theorem m3644_160 : Upper (D 10) (R 10) [12,65,160] 13 :=
  permutation_upper _ _ _ [10,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3485

theorem m3644_192 : Upper (D 10) (R 10) [12,65,192] 13 :=
  permutation_upper _ _ _ [10,192,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3490

theorem m3644_384 : Upper (D 10) (R 10) [12,65,384] 13 :=
  permutation_upper _ _ _ [10,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3493

def r3644 : Route 9 := (fun mask => match mask with | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3644 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3644 : Upper (D 10) (R 10) [12,65] 13 := by
  apply FastRouting.sound _ _ [12,65] 13 (by decide) (choices 2) [18,34,48,66,80,96,130,144,160,192,384] r3644 c3644
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3644_18
  · exact m3644_34
  · exact m3644_48
  · exact m3644_66
  · exact m3644_80
  · exact m3644_96
  · exact m3644_130
  · exact m3644_144
  · exact m3644_160
  · exact m3644_192
  · exact m3644_384

theorem m3645_3 : Upper (D 10) (R 10) [12,96,3] 13 :=
  permutation_upper _ _ _ [6,9,96] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3415

theorem m3645_17 : Upper (D 10) (R 10) [12,96,17] 13 :=
  permutation_upper _ _ _ [10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3448

theorem m3645_18 : Upper (D 10) (R 10) [12,96,18] 13 :=
  permutation_upper _ _ _ [10,20,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3452

theorem m3645_33 : Upper (D 10) (R 10) [12,96,33] 13 :=
  permutation_upper _ _ _ [10,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3454

theorem m3645_34 : Upper (D 10) (R 10) [12,96,34] 13 :=
  permutation_upper _ _ _ [10,36,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3458

theorem m3645_48 : Upper (D 10) (R 10) [12,96,48] 13 :=
  permutation_upper _ _ _ [10,48,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3462

theorem m3645_65 : Upper (D 10) (R 10) [12,96,65] 13 :=
  permutation_upper _ _ _ [10,65,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3464

theorem m3645_66 : Upper (D 10) (R 10) [12,96,66] 13 :=
  permutation_upper _ _ _ [10,68,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3470

theorem m3645_80 : Upper (D 10) (R 10) [12,96,80] 13 :=
  permutation_upper _ _ _ [10,80,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3477

theorem m3645_96 : Upper (D 10) (R 10) [12,96,96] 13 :=
  permutation_upper _ _ _ [10,96,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3484

theorem m3645_129 : Upper (D 10) (R 10) [12,96,129] 13 :=
  permutation_upper _ _ _ [10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3465

theorem m3645_130 : Upper (D 10) (R 10) [12,96,130] 13 :=
  permutation_upper _ _ _ [10,68,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3472

theorem m3645_144 : Upper (D 10) (R 10) [12,96,144] 13 :=
  permutation_upper _ _ _ [10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3479

theorem m3645_160 : Upper (D 10) (R 10) [12,96,160] 13 :=
  permutation_upper _ _ _ [10,96,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3486

theorem m3645_192 : Upper (D 10) (R 10) [12,96,192] 13 :=
  permutation_upper _ _ _ [10,192,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3491

theorem m3645_384 : Upper (D 10) (R 10) [12,96,384] 13 :=
  permutation_upper _ _ _ [10,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3494

def r3645 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 272 => (144,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3645 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3645 : Upper (D 10) (R 10) [12,96] 13 := by
  apply FastRouting.sound _ _ [12,96] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,129,130,144,160,192,384] r3645 c3645
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3645_3
  · exact m3645_17
  · exact m3645_18
  · exact m3645_33
  · exact m3645_34
  · exact m3645_48
  · exact m3645_65
  · exact m3645_66
  · exact m3645_80
  · exact m3645_96
  · exact m3645_129
  · exact m3645_130
  · exact m3645_144
  · exact m3645_160
  · exact m3645_192
  · exact m3645_384

theorem m3646_3 : Upper (D 10) (R 10) [12,192,3] 13 :=
  permutation_upper _ _ _ [6,9,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3416

theorem m3646_17 : Upper (D 10) (R 10) [12,192,17] 13 :=
  permutation_upper _ _ _ [10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3449

theorem m3646_18 : Upper (D 10) (R 10) [12,192,18] 13 :=
  permutation_upper _ _ _ [10,20,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3453

theorem m3646_33 : Upper (D 10) (R 10) [12,192,33] 13 :=
  permutation_upper _ _ _ [10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3455

theorem m3646_34 : Upper (D 10) (R 10) [12,192,34] 13 :=
  permutation_upper _ _ _ [10,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3459

theorem m3646_48 : Upper (D 10) (R 10) [12,192,48] 13 :=
  permutation_upper _ _ _ [10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3463

theorem m3646_65 : Upper (D 10) (R 10) [12,192,65] 13 :=
  permutation_upper _ _ _ [10,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3466

theorem m3646_66 : Upper (D 10) (R 10) [12,192,66] 13 :=
  permutation_upper _ _ _ [10,68,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3473

theorem m3646_80 : Upper (D 10) (R 10) [12,192,80] 13 :=
  permutation_upper _ _ _ [10,80,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3480

theorem m3646_96 : Upper (D 10) (R 10) [12,192,96] 13 :=
  permutation_upper _ _ _ [10,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3487

theorem m3646_192 : Upper (D 10) (R 10) [12,192,192] 13 :=
  permutation_upper _ _ _ [10,192,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3492

theorem m3646_257 : Upper (D 10) (R 10) [12,192,257] 13 :=
  permutation_upper _ _ _ [10,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3467

theorem m3646_258 : Upper (D 10) (R 10) [12,192,258] 13 :=
  permutation_upper _ _ _ [10,68,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3474

theorem m3646_272 : Upper (D 10) (R 10) [12,192,272] 13 :=
  permutation_upper _ _ _ [10,80,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3481

theorem m3646_288 : Upper (D 10) (R 10) [12,192,288] 13 :=
  permutation_upper _ _ _ [10,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3488

theorem m3646_320 : Upper (D 10) (R 10) [12,192,320] 13 :=
  permutation_upper _ _ _ [10,192,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3495

def r3646 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3646 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 10 => 3 | 24 => 3 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3646 : Upper (D 10) (R 10) [12,192] 13 := by
  apply FastRouting.sound _ _ [12,192] 13 (by decide) (choices 2) [3,17,18,33,34,48,65,66,80,96,192,257,258,272,288,320] r3646 c3646
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3646_3
  · exact m3646_17
  · exact m3646_18
  · exact m3646_33
  · exact m3646_34
  · exact m3646_48
  · exact m3646_65
  · exact m3646_66
  · exact m3646_80
  · exact m3646_96
  · exact m3646_192
  · exact m3646_257
  · exact m3646_258
  · exact m3646_272
  · exact m3646_288
  · exact m3646_320

def b3647 : PairBound 9 := { available := 508, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 508 508 508 508 508 508 508), lower := (rows 35 35 4 8 16 32 64 128 256), losses := [] }

theorem u3647 : Upper (D 10) (R 10) [34,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3647 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3648 : PairBound 9 := { available := 505, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 509 505 505 505 505 505 505), lower := (rows 35 38 4 8 16 32 64 128 256), losses := [] }

theorem u3648 : Upper (D 10) (R 10) [34,36] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3648 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3649_24 : Upper (D 10) (R 10) [34,65,24] 13 :=
  permutation_upper _ _ _ [24,36,66] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3500

def r3649 : Route 9 := (fun mask => match mask with | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3649 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3649 : Upper (D 10) (R 10) [34,65] 13 := by
  apply FastRouting.sound _ _ [34,65] 13 (by decide) (choices 2) [24,40,72,96,136,160,192,384] r3649 c3649
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3649_24
  · exact u3522
  · exact u3523
  · exact u3524
  · exact u3525
  · exact u3526
  · exact u3527
  · exact u3528

theorem m3650_9 : Upper (D 10) (R 10) [34,68,9] 13 :=
  permutation_upper _ _ _ [10,36,65] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3457

theorem m3650_24 : Upper (D 10) (R 10) [34,68,24] 13 :=
  permutation_upper _ _ _ [24,36,65] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3499

theorem m3650_33 : Upper (D 10) (R 10) [34,68,33] 13 :=
  permutation_upper _ _ _ [34,36,65] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3516

def r3650 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3650 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3650 : Upper (D 10) (R 10) [34,68] 13 := by
  apply FastRouting.sound _ _ [34,68] 13 (by decide) (choices 2) [9,24,33,40,65,72,96,129,136,160,192,384] r3650 c3650
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3650_9
  · exact m3650_24
  · exact m3650_33
  · exact u3529
  · exact u3530
  · exact u3531
  · exact u3532
  · exact u3533
  · exact u3534
  · exact u3535
  · exact u3536
  · exact u3537

def b3651 : PairBound 9 := { available := 509, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 98 509 509 509 509 509 509 509), lower := (rows 35 98 4 8 16 32 64 128 256), losses := [] }

theorem u3651 : Upper (D 10) (R 10) [34,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3651 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3652_9 : Upper (D 10) (R 10) [34,192,9] 13 :=
  permutation_upper _ _ _ [10,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3459

theorem m3652_24 : Upper (D 10) (R 10) [34,192,24] 13 :=
  permutation_upper _ _ _ [24,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3501

theorem m3652_33 : Upper (D 10) (R 10) [34,192,33] 13 :=
  permutation_upper _ _ _ [34,36,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3518

def r3652 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3652 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3652 : Upper (D 10) (R 10) [34,192] 13 := by
  apply FastRouting.sound _ _ [34,192] 13 (by decide) (choices 2) [9,24,33,40,65,72,96,192,257,264,288,320] r3652 c3652
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3652_9
  · exact m3652_24
  · exact m3652_33
  · exact u3550
  · exact u3551
  · exact u3552
  · exact u3553
  · exact u3554
  · exact u3555
  · exact u3556
  · exact u3557
  · exact u3558

theorem m3653_10 : Upper (D 10) (R 10) [36,65,10] 13 :=
  permutation_upper _ _ _ [10,68,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3468

theorem m3653_24 : Upper (D 10) (R 10) [36,65,24] 13 :=
  permutation_upper _ _ _ [24,33,66] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3496

theorem m3653_34 : Upper (D 10) (R 10) [36,65,34] 13 :=
  permutation_upper _ _ _ [34,36,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3516

theorem m3653_40 : Upper (D 10) (R 10) [36,65,40] 13 :=
  permutation_upper _ _ _ [34,40,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3519

theorem m3653_66 : Upper (D 10) (R 10) [36,65,66] 13 :=
  permutation_upper _ _ _ [34,68,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3530

theorem m3653_72 : Upper (D 10) (R 10) [36,65,72] 13 :=
  permutation_upper _ _ _ [34,72,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3538

theorem m3653_96 : Upper (D 10) (R 10) [36,65,96] 13 :=
  permutation_upper _ _ _ [34,96,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3544

theorem m3653_130 : Upper (D 10) (R 10) [36,65,130] 13 :=
  permutation_upper _ _ _ [34,68,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3533

theorem m3653_136 : Upper (D 10) (R 10) [36,65,136] 13 :=
  permutation_upper _ _ _ [34,72,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3540

theorem m3653_160 : Upper (D 10) (R 10) [36,65,160] 13 :=
  permutation_upper _ _ _ [34,96,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3546

theorem m3653_192 : Upper (D 10) (R 10) [36,65,192] 13 :=
  permutation_upper _ _ _ [34,192,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3551

theorem m3653_384 : Upper (D 10) (R 10) [36,65,384] 13 :=
  permutation_upper _ _ _ [34,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3555

def r3653 : Route 9 := (fun mask => match mask with | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3653 : Nat → Fin 9 := (fun _ => 0)

theorem u3653 : Upper (D 10) (R 10) [36,65] 13 := by
  apply FastRouting.sound _ _ [36,65] 13 (by decide) (choices 2) [10,24,34,40,66,72,96,130,136,160,192,384] r3653 c3653
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3653_10
  · exact m3653_24
  · exact m3653_34
  · exact m3653_40
  · exact m3653_66
  · exact m3653_72
  · exact m3653_96
  · exact m3653_130
  · exact m3653_136
  · exact m3653_160
  · exact m3653_192
  · exact m3653_384

theorem m3654_3 : Upper (D 10) (R 10) [36,96,3] 13 :=
  permutation_upper _ _ _ [6,33,96] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3423

theorem m3654_9 : Upper (D 10) (R 10) [36,96,9] 13 :=
  permutation_upper _ _ _ [10,33,96] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3454

theorem m3654_10 : Upper (D 10) (R 10) [36,96,10] 13 :=
  permutation_upper _ _ _ [10,96,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3482

theorem m3654_24 : Upper (D 10) (R 10) [36,96,24] 13 :=
  permutation_upper _ _ _ [24,33,96] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3497

theorem m3654_33 : Upper (D 10) (R 10) [36,96,33] 13 :=
  permutation_upper _ _ _ [34,33,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3514

theorem m3654_34 : Upper (D 10) (R 10) [36,96,34] 13 :=
  permutation_upper _ _ _ [34,36,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3517

theorem m3654_40 : Upper (D 10) (R 10) [36,96,40] 13 :=
  permutation_upper _ _ _ [34,40,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3520

theorem m3654_65 : Upper (D 10) (R 10) [36,96,65] 13 :=
  permutation_upper _ _ _ [34,65,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3524

theorem m3654_66 : Upper (D 10) (R 10) [36,96,66] 13 :=
  permutation_upper _ _ _ [34,68,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3532

theorem m3654_72 : Upper (D 10) (R 10) [36,96,72] 13 :=
  permutation_upper _ _ _ [34,72,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3539

theorem m3654_96 : Upper (D 10) (R 10) [36,96,96] 13 :=
  permutation_upper _ _ _ [34,96,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3545

theorem m3654_129 : Upper (D 10) (R 10) [36,96,129] 13 :=
  permutation_upper _ _ _ [34,65,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3526

theorem m3654_130 : Upper (D 10) (R 10) [36,96,130] 13 :=
  permutation_upper _ _ _ [34,68,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3535

theorem m3654_136 : Upper (D 10) (R 10) [36,96,136] 13 :=
  permutation_upper _ _ _ [34,72,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3541

theorem m3654_160 : Upper (D 10) (R 10) [36,96,160] 13 :=
  permutation_upper _ _ _ [34,96,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3547

theorem m3654_192 : Upper (D 10) (R 10) [36,96,192] 13 :=
  permutation_upper _ _ _ [34,192,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3553

theorem m3654_384 : Upper (D 10) (R 10) [36,96,384] 13 :=
  permutation_upper _ _ _ [34,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3557

def r3654 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 320 => (192,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3654 : Nat → Fin 9 := (fun _ => 0)

theorem u3654 : Upper (D 10) (R 10) [36,96] 13 := by
  apply FastRouting.sound _ _ [36,96] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,129,130,136,160,192,384] r3654 c3654
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3654_3
  · exact m3654_9
  · exact m3654_10
  · exact m3654_24
  · exact m3654_33
  · exact m3654_34
  · exact m3654_40
  · exact m3654_65
  · exact m3654_66
  · exact m3654_72
  · exact m3654_96
  · exact m3654_129
  · exact m3654_130
  · exact m3654_136
  · exact m3654_160
  · exact m3654_192
  · exact m3654_384

theorem m3655_3 : Upper (D 10) (R 10) [36,192,3] 13 :=
  permutation_upper _ _ _ [6,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3424

theorem m3655_9 : Upper (D 10) (R 10) [36,192,9] 13 :=
  permutation_upper _ _ _ [10,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3455

theorem m3655_10 : Upper (D 10) (R 10) [36,192,10] 13 :=
  permutation_upper _ _ _ [10,192,33] (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3489

theorem m3655_24 : Upper (D 10) (R 10) [36,192,24] 13 :=
  permutation_upper _ _ _ [24,33,192] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3498

theorem m3655_33 : Upper (D 10) (R 10) [36,192,33] 13 :=
  permutation_upper _ _ _ [34,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3515

theorem m3655_34 : Upper (D 10) (R 10) [36,192,34] 13 :=
  permutation_upper _ _ _ [34,36,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3518

theorem m3655_40 : Upper (D 10) (R 10) [36,192,40] 13 :=
  permutation_upper _ _ _ [34,40,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3521

theorem m3655_65 : Upper (D 10) (R 10) [36,192,65] 13 :=
  permutation_upper _ _ _ [34,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3527

theorem m3655_66 : Upper (D 10) (R 10) [36,192,66] 13 :=
  permutation_upper _ _ _ [34,68,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3536

theorem m3655_72 : Upper (D 10) (R 10) [36,192,72] 13 :=
  permutation_upper _ _ _ [34,72,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3542

theorem m3655_96 : Upper (D 10) (R 10) [36,192,96] 13 :=
  permutation_upper _ _ _ [34,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3548

theorem m3655_192 : Upper (D 10) (R 10) [36,192,192] 13 :=
  permutation_upper _ _ _ [34,192,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3554

theorem m3655_257 : Upper (D 10) (R 10) [36,192,257] 13 :=
  permutation_upper _ _ _ [34,65,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3528

theorem m3655_258 : Upper (D 10) (R 10) [36,192,258] 13 :=
  permutation_upper _ _ _ [34,68,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3537

theorem m3655_264 : Upper (D 10) (R 10) [36,192,264] 13 :=
  permutation_upper _ _ _ [34,72,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3543

theorem m3655_288 : Upper (D 10) (R 10) [36,192,288] 13 :=
  permutation_upper _ _ _ [34,96,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3549

theorem m3655_320 : Upper (D 10) (R 10) [36,192,320] 13 :=
  permutation_upper _ _ _ [34,192,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3558

def r3655 : Route 9 := (fun mask => match mask with | 17 => (9,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 18 => (10,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | 6 => 7 | 7 => 6 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c3655 : Nat → Fin 9 := (fun _ => 0)

theorem u3655 : Upper (D 10) (R 10) [36,192] 13 := by
  apply FastRouting.sound _ _ [36,192] 13 (by decide) (choices 2) [3,9,10,24,33,34,40,65,66,72,96,192,257,258,264,288,320] r3655 c3655
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3655_3
  · exact m3655_9
  · exact m3655_10
  · exact m3655_24
  · exact m3655_33
  · exact m3655_34
  · exact m3655_40
  · exact m3655_65
  · exact m3655_66
  · exact m3655_72
  · exact m3655_96
  · exact m3655_192
  · exact m3655_257
  · exact m3655_258
  · exact m3655_264
  · exact m3655_288
  · exact m3655_320

def b3656 : PairBound 9 := { available := 444, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 444 444 444 444 508 444 444), lower := (rows 67 67 4 8 16 32 64 128 256), losses := [] }

theorem u3656 : Upper (D 10) (R 10) [66,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3656 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3657 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 445 441 441 441 505 441 441), lower := (rows 67 70 4 8 16 32 64 128 256), losses := [] }

theorem u3657 : Upper (D 10) (R 10) [66,68] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3657 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3658 : PairBound 9 := { available := 445, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 445 445 445 445 509 445 445), lower := (rows 67 98 4 8 16 32 64 128 256), losses := [] }

theorem u3658 : Upper (D 10) (R 10) [66,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3658 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3659_24 : Upper (D 10) (R 10) [66,129,24] 13 :=
  permutation_upper _ _ _ [24,68,130] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3507

theorem m3659_40 : Upper (D 10) (R 10) [66,129,40] 13 :=
  permutation_upper _ _ _ [40,68,130] (fun i => match i.val with | 0 => 2 | 1 => 0 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 0 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3564

theorem m3659_136 : Upper (D 10) (R 10) [66,129,136] 13 :=
  permutation_upper _ _ _ [66,129,72] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3582

theorem m3659_160 : Upper (D 10) (R 10) [66,129,160] 13 :=
  permutation_upper _ _ _ [66,129,96] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3583

theorem m3659_384 : Upper (D 10) (R 10) [66,129,384] 13 :=
  permutation_upper _ _ _ [66,129,320] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3587

def r3659 : Route 9 := (fun mask => match mask with | 48 => (40,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 80 => (72,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 144 => (136,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | 272 => (264,(fun i => match i.val with | 3 => 4 | 4 => 3 | _ => i)) | _ => (mask,id))

def c3659 : Nat → Fin 9 := (fun mask => match mask with | 10 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u3659 : Upper (D 10) (R 10) [66,129] 13 := by
  apply FastRouting.sound _ _ [66,129] 13 (by decide) (choices 2) [24,40,72,96,136,160,192,264,288,320,384] r3659 c3659
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3659_24
  · exact m3659_40
  · exact u3582
  · exact u3583
  · exact m3659_136
  · exact m3659_160
  · exact u3584
  · exact u3585
  · exact u3586
  · exact u3587
  · exact m3659_384

#print axioms u3659
end Delivery.IrregularNine14.P10
