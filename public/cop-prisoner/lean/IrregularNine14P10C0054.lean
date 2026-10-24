import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0020
import IrregularNine14P10C0021
import IrregularNine14P10C0024
import IrregularNine14P10C0025
import IrregularNine14P10C0026
import IrregularNine14P10C0027
import IrregularNine14P10C0028
import IrregularNine14P10C0029
import IrregularNine14P10C0030
import IrregularNine14P10C0031
import IrregularNine14P10C0032
import IrregularNine14P10C0033
import IrregularNine14P10C0034
import IrregularNine14P10C0035
import IrregularNine14P10C0036
import IrregularNine14P10C0037
import IrregularNine14P10C0038
import IrregularNine14P10C0039
import IrregularNine14P10C0040

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m3240_9 : Upper (D 10) (R 10) [48,68,130,288,9] 13 :=
  permutation_upper _ _ _ [6,33,96,144,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1250

theorem m3240_33 : Upper (D 10) (R 10) [48,68,130,288,33] 13 :=
  permutation_upper _ _ _ [34,33,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1848

theorem m3240_40 : Upper (D 10) (R 10) [48,68,130,288,40] 13 :=
  permutation_upper _ _ _ [34,36,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1909

theorem m3240_65 : Upper (D 10) (R 10) [48,68,130,288,65] 13 :=
  permutation_upper _ _ _ [34,65,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1967

theorem m3240_72 : Upper (D 10) (R 10) [48,68,130,288,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2178

theorem m3240_96 : Upper (D 10) (R 10) [48,68,130,288,96] 13 :=
  permutation_upper _ _ _ [34,96,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2264

theorem m3240_129 : Upper (D 10) (R 10) [48,68,130,288,129] 13 :=
  permutation_upper _ _ _ [34,65,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1967

theorem m3240_136 : Upper (D 10) (R 10) [48,68,130,288,136] 13 :=
  permutation_upper _ _ _ [34,68,160,80,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2178

theorem m3240_160 : Upper (D 10) (R 10) [48,68,130,288,160] 13 :=
  permutation_upper _ _ _ [34,96,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2264

theorem m3240_192 : Upper (D 10) (R 10) [48,68,130,288,192] 13 :=
  permutation_upper _ _ _ [34,192,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2320

theorem m3240_257 : Upper (D 10) (R 10) [48,68,130,288,257] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1981

theorem m3240_264 : Upper (D 10) (R 10) [48,68,130,288,264] 13 :=
  permutation_upper _ _ _ [34,68,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2067

theorem m3240_288 : Upper (D 10) (R 10) [48,68,130,288,288] 13 :=
  permutation_upper _ _ _ [34,96,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2280

theorem m3240_320 : Upper (D 10) (R 10) [48,68,130,288,320] 13 :=
  permutation_upper _ _ _ [34,192,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2331

theorem m3240_384 : Upper (D 10) (R 10) [48,68,130,288,384] 13 :=
  permutation_upper _ _ _ [34,192,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2331

def r3240 : Route 9 := (fun mask => (mask,id))

def c3240 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u3240 : Upper (D 10) (R 10) [48,68,130,288] 13 := by
  apply FastRouting.sound _ _ [48,68,130,288] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r3240 c3240
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3240_9
  · exact m3240_33
  · exact m3240_40
  · exact m3240_65
  · exact m3240_72
  · exact m3240_96
  · exact m3240_129
  · exact m3240_136
  · exact m3240_160
  · exact m3240_192
  · exact m3240_257
  · exact m3240_264
  · exact m3240_288
  · exact m3240_320
  · exact m3240_384

theorem m3241_33 : Upper (D 10) (R 10) [48,68,136,258,33] 13 :=
  permutation_upper _ _ _ [34,33,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1849

theorem m3241_65 : Upper (D 10) (R 10) [48,68,136,258,65] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1969

theorem m3241_96 : Upper (D 10) (R 10) [48,68,136,258,96] 13 :=
  permutation_upper _ _ _ [34,96,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2266

theorem m3241_129 : Upper (D 10) (R 10) [48,68,136,258,129] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1969

theorem m3241_160 : Upper (D 10) (R 10) [48,68,136,258,160] 13 :=
  permutation_upper _ _ _ [34,96,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2266

theorem m3241_192 : Upper (D 10) (R 10) [48,68,136,258,192] 13 :=
  permutation_upper _ _ _ [34,192,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2322

theorem m3241_257 : Upper (D 10) (R 10) [48,68,136,258,257] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1969

theorem m3241_288 : Upper (D 10) (R 10) [48,68,136,258,288] 13 :=
  permutation_upper _ _ _ [34,96,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2266

theorem m3241_320 : Upper (D 10) (R 10) [48,68,136,258,320] 13 :=
  permutation_upper _ _ _ [34,192,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2322

theorem m3241_384 : Upper (D 10) (R 10) [48,68,136,258,384] 13 :=
  permutation_upper _ _ _ [34,192,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2322

def r3241 : Route 9 := (fun mask => (mask,id))

def c3241 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3241 : Upper (D 10) (R 10) [48,68,136,258] 13 := by
  apply FastRouting.sound _ _ [48,68,136,258] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r3241 c3241
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3241_33
  · exact m3241_65
  · exact m3241_96
  · exact m3241_129
  · exact m3241_160
  · exact m3241_192
  · exact m3241_257
  · exact m3241_288
  · exact m3241_320
  · exact m3241_384

theorem m3242_3 : Upper (D 10) (R 10) [48,68,136,288,3] 13 :=
  permutation_upper _ _ _ [6,33,72,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1225

theorem m3242_33 : Upper (D 10) (R 10) [48,68,136,288,33] 13 :=
  permutation_upper _ _ _ [34,33,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1850

theorem m3242_34 : Upper (D 10) (R 10) [48,68,136,288,34] 13 :=
  permutation_upper _ _ _ [34,36,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1889

theorem m3242_65 : Upper (D 10) (R 10) [48,68,136,288,65] 13 :=
  permutation_upper _ _ _ [34,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1970

theorem m3242_66 : Upper (D 10) (R 10) [48,68,136,288,66] 13 :=
  permutation_upper _ _ _ [34,68,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2055

theorem m3242_96 : Upper (D 10) (R 10) [48,68,136,288,96] 13 :=
  permutation_upper _ _ _ [34,96,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2267

theorem m3242_129 : Upper (D 10) (R 10) [48,68,136,288,129] 13 :=
  permutation_upper _ _ _ [34,65,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1972

theorem m3242_130 : Upper (D 10) (R 10) [48,68,136,288,130] 13 :=
  permutation_upper _ _ _ [34,68,136,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2114

theorem m3242_160 : Upper (D 10) (R 10) [48,68,136,288,160] 13 :=
  permutation_upper _ _ _ [34,96,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2270

theorem m3242_192 : Upper (D 10) (R 10) [48,68,136,288,192] 13 :=
  permutation_upper _ _ _ [34,192,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2323

theorem m3242_257 : Upper (D 10) (R 10) [48,68,136,288,257] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1978

theorem m3242_258 : Upper (D 10) (R 10) [48,68,136,288,258] 13 :=
  permutation_upper _ _ _ [34,68,136,272,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2141

theorem m3242_288 : Upper (D 10) (R 10) [48,68,136,288,288] 13 :=
  permutation_upper _ _ _ [34,96,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2278

theorem m3242_320 : Upper (D 10) (R 10) [48,68,136,288,320] 13 :=
  permutation_upper _ _ _ [34,192,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2335

theorem m3242_384 : Upper (D 10) (R 10) [48,68,136,288,384] 13 :=
  permutation_upper _ _ _ [34,192,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2325

def r3242 : Route 9 := (fun mask => (mask,id))

def c3242 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u3242 : Upper (D 10) (R 10) [48,68,136,288] 13 := by
  apply FastRouting.sound _ _ [48,68,136,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192,257,258,288,320,384] r3242 c3242
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3242_3
  · exact m3242_33
  · exact m3242_34
  · exact m3242_65
  · exact m3242_66
  · exact m3242_96
  · exact m3242_129
  · exact m3242_130
  · exact m3242_160
  · exact m3242_192
  · exact m3242_257
  · exact m3242_258
  · exact m3242_288
  · exact m3242_320
  · exact m3242_384

theorem m3243_3 : Upper (D 10) (R 10) [48,68,160,96,3] 13 :=
  permutation_upper _ _ _ [6,33,72,160,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1228

theorem m3243_9 : Upper (D 10) (R 10) [48,68,160,96,9] 13 :=
  permutation_upper _ _ _ [6,33,96,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1246

theorem m3243_10 : Upper (D 10) (R 10) [48,68,160,96,10] 13 :=
  permutation_upper _ _ _ [6,72,96,160,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1555

theorem m3243_129 : Upper (D 10) (R 10) [48,68,160,96,129] 13 :=
  permutation_upper _ _ _ [34,65,96,132,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1977

theorem m3243_130 : Upper (D 10) (R 10) [48,68,160,96,130] 13 :=
  permutation_upper _ _ _ [34,68,136,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2117

theorem m3243_136 : Upper (D 10) (R 10) [48,68,160,96,136] 13 :=
  permutation_upper _ _ _ [34,68,160,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2182

theorem m3243_257 : Upper (D 10) (R 10) [48,68,160,96,257] 13 :=
  permutation_upper _ _ _ [34,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1997

theorem m3243_258 : Upper (D 10) (R 10) [48,68,160,96,258] 13 :=
  permutation_upper _ _ _ [34,68,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2152

theorem m3243_264 : Upper (D 10) (R 10) [48,68,160,96,264] 13 :=
  permutation_upper _ _ _ [34,68,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2191

theorem m3243_384 : Upper (D 10) (R 10) [48,68,160,96,384] 13 :=
  permutation_upper _ _ _ [34,192,96,260,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2355

def r3243 : Route 9 := (fun mask => (mask,id))

def c3243 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 2 | 34 => 5 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3243 : Upper (D 10) (R 10) [48,68,160,96] 13 := by
  apply FastRouting.sound _ _ [48,68,160,96] 13 (by decide) (choices 2) [3,9,10,129,130,136,257,258,264,384] r3243 c3243
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3243_3
  · exact m3243_9
  · exact m3243_10
  · exact m3243_129
  · exact m3243_130
  · exact m3243_136
  · exact m3243_257
  · exact m3243_258
  · exact m3243_264
  · exact m3243_384

theorem m3244_3 : Upper (D 10) (R 10) [48,68,160,192,3] 13 :=
  permutation_upper _ _ _ [6,33,72,160,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1230

theorem m3244_9 : Upper (D 10) (R 10) [48,68,160,192,9] 13 :=
  permutation_upper _ _ _ [6,33,192,80,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1265

theorem m3244_10 : Upper (D 10) (R 10) [48,68,160,192,10] 13 :=
  permutation_upper _ _ _ [6,72,192,160,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1677

theorem m3244_33 : Upper (D 10) (R 10) [48,68,160,192,33] 13 :=
  permutation_upper _ _ _ [34,33,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1851

theorem m3244_34 : Upper (D 10) (R 10) [48,68,160,192,34] 13 :=
  permutation_upper _ _ _ [34,36,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1892

theorem m3244_40 : Upper (D 10) (R 10) [48,68,160,192,40] 13 :=
  permutation_upper _ _ _ [34,36,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1921

theorem m3244_257 : Upper (D 10) (R 10) [48,68,160,192,257] 13 :=
  permutation_upper _ _ _ [34,65,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2001

theorem m3244_258 : Upper (D 10) (R 10) [48,68,160,192,258] 13 :=
  permutation_upper _ _ _ [34,68,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2157

theorem m3244_264 : Upper (D 10) (R 10) [48,68,160,192,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2240

theorem m3244_288 : Upper (D 10) (R 10) [48,68,160,192,288] 13 :=
  permutation_upper _ _ _ [34,96,136,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2297

def r3244 : Route 9 := (fun mask => (mask,id))

def c3244 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3244 : Upper (D 10) (R 10) [48,68,160,192] 13 := by
  apply FastRouting.sound _ _ [48,68,160,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r3244 c3244
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3244_3
  · exact m3244_9
  · exact m3244_10
  · exact m3244_33
  · exact m3244_34
  · exact m3244_40
  · exact m3244_257
  · exact m3244_258
  · exact m3244_264
  · exact m3244_288

theorem m3245_3 : Upper (D 10) (R 10) [48,68,160,288,3] 13 :=
  permutation_upper _ _ _ [6,33,72,160,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1231

theorem m3245_9 : Upper (D 10) (R 10) [48,68,160,288,9] 13 :=
  permutation_upper _ _ _ [6,33,96,144,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1251

theorem m3245_10 : Upper (D 10) (R 10) [48,68,160,288,10] 13 :=
  permutation_upper _ _ _ [6,72,160,288,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1647

theorem m3245_65 : Upper (D 10) (R 10) [48,68,160,288,65] 13 :=
  permutation_upper _ _ _ [34,65,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1973

theorem m3245_66 : Upper (D 10) (R 10) [48,68,160,288,66] 13 :=
  permutation_upper _ _ _ [34,68,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2058

theorem m3245_72 : Upper (D 10) (R 10) [48,68,160,288,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2179

theorem m3245_129 : Upper (D 10) (R 10) [48,68,160,288,129] 13 :=
  permutation_upper _ _ _ [34,65,96,132,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1979

theorem m3245_130 : Upper (D 10) (R 10) [48,68,160,288,130] 13 :=
  permutation_upper _ _ _ [34,68,136,96,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2119

theorem m3245_136 : Upper (D 10) (R 10) [48,68,160,288,136] 13 :=
  permutation_upper _ _ _ [34,68,160,96,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2184

theorem m3245_192 : Upper (D 10) (R 10) [48,68,160,288,192] 13 :=
  permutation_upper _ _ _ [34,192,72,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2326

theorem m3245_257 : Upper (D 10) (R 10) [48,68,160,288,257] 13 :=
  permutation_upper _ _ _ [34,65,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1982

theorem m3245_258 : Upper (D 10) (R 10) [48,68,160,288,258] 13 :=
  permutation_upper _ _ _ [34,68,136,288,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2150

theorem m3245_264 : Upper (D 10) (R 10) [48,68,160,288,264] 13 :=
  permutation_upper _ _ _ [34,68,96,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2068

theorem m3245_320 : Upper (D 10) (R 10) [48,68,160,288,320] 13 :=
  permutation_upper _ _ _ [34,192,72,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2340

theorem m3245_384 : Upper (D 10) (R 10) [48,68,160,288,384] 13 :=
  permutation_upper _ _ _ [34,192,96,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2349

def r3245 : Route 9 := (fun mask => (mask,id))

def c3245 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 6 => 2 | 34 => 5 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u3245 : Upper (D 10) (R 10) [48,68,160,288] 13 := by
  apply FastRouting.sound _ _ [48,68,160,288] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192,257,258,264,320,384] r3245 c3245
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3245_3
  · exact m3245_9
  · exact m3245_10
  · exact m3245_65
  · exact m3245_66
  · exact m3245_72
  · exact m3245_129
  · exact m3245_130
  · exact m3245_136
  · exact m3245_192
  · exact m3245_257
  · exact m3245_258
  · exact m3245_264
  · exact m3245_320
  · exact m3245_384

theorem m3246_3 : Upper (D 10) (R 10) [48,68,160,320,3] 13 :=
  permutation_upper _ _ _ [6,33,72,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1232

theorem m3246_9 : Upper (D 10) (R 10) [48,68,160,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,80,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1267

theorem m3246_10 : Upper (D 10) (R 10) [48,68,160,320,10] 13 :=
  permutation_upper _ _ _ [6,72,192,288,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1686

theorem m3246_33 : Upper (D 10) (R 10) [48,68,160,320,33] 13 :=
  permutation_upper _ _ _ [34,33,72,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1852

theorem m3246_34 : Upper (D 10) (R 10) [48,68,160,320,34] 13 :=
  permutation_upper _ _ _ [34,36,72,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1894

theorem m3246_40 : Upper (D 10) (R 10) [48,68,160,320,40] 13 :=
  permutation_upper _ _ _ [34,36,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1923

theorem m3246_129 : Upper (D 10) (R 10) [48,68,160,320,129] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1980

theorem m3246_130 : Upper (D 10) (R 10) [48,68,160,320,130] 13 :=
  permutation_upper _ _ _ [34,68,136,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2120

theorem m3246_136 : Upper (D 10) (R 10) [48,68,160,320,136] 13 :=
  permutation_upper _ _ _ [34,68,384,96,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2233

theorem m3246_160 : Upper (D 10) (R 10) [48,68,160,320,160] 13 :=
  permutation_upper _ _ _ [34,96,96,132,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2279

theorem m3246_257 : Upper (D 10) (R 10) [48,68,160,320,257] 13 :=
  permutation_upper _ _ _ [34,65,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1998

theorem m3246_258 : Upper (D 10) (R 10) [48,68,160,320,258] 13 :=
  permutation_upper _ _ _ [34,68,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2153

theorem m3246_264 : Upper (D 10) (R 10) [48,68,160,320,264] 13 :=
  permutation_upper _ _ _ [34,68,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2215

theorem m3246_288 : Upper (D 10) (R 10) [48,68,160,320,288] 13 :=
  permutation_upper _ _ _ [34,96,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2295

theorem m3246_384 : Upper (D 10) (R 10) [48,68,160,320,384] 13 :=
  permutation_upper _ _ _ [34,192,96,260,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2356

def r3246 : Route 9 := (fun mask => (mask,id))

def c3246 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3246 : Upper (D 10) (R 10) [48,68,160,320] 13 := by
  apply FastRouting.sound _ _ [48,68,160,320] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,257,258,264,288,384] r3246 c3246
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3246_3
  · exact m3246_9
  · exact m3246_10
  · exact m3246_33
  · exact m3246_34
  · exact m3246_40
  · exact m3246_129
  · exact m3246_130
  · exact m3246_136
  · exact m3246_160
  · exact m3246_257
  · exact m3246_258
  · exact m3246_264
  · exact m3246_288
  · exact m3246_384

theorem m3247_3 : Upper (D 10) (R 10) [48,68,160,384,3] 13 :=
  permutation_upper _ _ _ [6,33,72,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1233

theorem m3247_9 : Upper (D 10) (R 10) [48,68,160,384,9] 13 :=
  permutation_upper _ _ _ [6,33,192,96,264] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1270

theorem m3247_10 : Upper (D 10) (R 10) [48,68,160,384,10] 13 :=
  permutation_upper _ _ _ [6,72,384,160,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1719

theorem m3247_33 : Upper (D 10) (R 10) [48,68,160,384,33] 13 :=
  permutation_upper _ _ _ [34,33,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1853

theorem m3247_34 : Upper (D 10) (R 10) [48,68,160,384,34] 13 :=
  permutation_upper _ _ _ [34,36,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1895

theorem m3247_40 : Upper (D 10) (R 10) [48,68,160,384,40] 13 :=
  permutation_upper _ _ _ [34,36,192,96,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1926

theorem m3247_65 : Upper (D 10) (R 10) [48,68,160,384,65] 13 :=
  permutation_upper _ _ _ [34,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1974

theorem m3247_66 : Upper (D 10) (R 10) [48,68,160,384,66] 13 :=
  permutation_upper _ _ _ [34,68,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2059

theorem m3247_72 : Upper (D 10) (R 10) [48,68,160,384,72] 13 :=
  permutation_upper _ _ _ [34,68,384,80,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2230

theorem m3247_96 : Upper (D 10) (R 10) [48,68,160,384,96] 13 :=
  permutation_upper _ _ _ [34,96,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2271

theorem m3247_257 : Upper (D 10) (R 10) [48,68,160,384,257] 13 :=
  permutation_upper _ _ _ [34,65,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2000

theorem m3247_258 : Upper (D 10) (R 10) [48,68,160,384,258] 13 :=
  permutation_upper _ _ _ [34,68,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2156

theorem m3247_264 : Upper (D 10) (R 10) [48,68,160,384,264] 13 :=
  permutation_upper _ _ _ [34,68,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2217

theorem m3247_288 : Upper (D 10) (R 10) [48,68,160,384,288] 13 :=
  permutation_upper _ _ _ [34,96,136,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2296

theorem m3247_320 : Upper (D 10) (R 10) [48,68,160,384,320] 13 :=
  permutation_upper _ _ _ [34,192,72,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2344

def r3247 : Route 9 := (fun mask => (mask,id))

def c3247 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3247 : Upper (D 10) (R 10) [48,68,160,384] 13 := by
  apply FastRouting.sound _ _ [48,68,160,384] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r3247 c3247
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3247_3
  · exact m3247_9
  · exact m3247_10
  · exact m3247_33
  · exact m3247_34
  · exact m3247_40
  · exact m3247_65
  · exact m3247_66
  · exact m3247_72
  · exact m3247_96
  · exact m3247_257
  · exact m3247_258
  · exact m3247_264
  · exact m3247_288
  · exact m3247_320

theorem m3248_3 : Upper (D 10) (R 10) [48,68,384,96,3] 13 :=
  permutation_upper _ _ _ [6,33,72,384,96] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1237

theorem m3248_9 : Upper (D 10) (R 10) [48,68,384,96,9] 13 :=
  permutation_upper _ _ _ [6,33,96,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1247

theorem m3248_10 : Upper (D 10) (R 10) [48,68,384,96,10] 13 :=
  permutation_upper _ _ _ [6,72,96,384,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1560

theorem m3248_33 : Upper (D 10) (R 10) [48,68,384,96,33] 13 :=
  permutation_upper _ _ _ [34,33,72,384,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1854

theorem m3248_34 : Upper (D 10) (R 10) [48,68,384,96,34] 13 :=
  permutation_upper _ _ _ [34,36,72,384,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1897

theorem m3248_40 : Upper (D 10) (R 10) [48,68,384,96,40] 13 :=
  permutation_upper _ _ _ [34,36,96,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1904

theorem m3248_129 : Upper (D 10) (R 10) [48,68,384,96,129] 13 :=
  permutation_upper _ _ _ [34,65,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2002

theorem m3248_130 : Upper (D 10) (R 10) [48,68,384,96,130] 13 :=
  permutation_upper _ _ _ [34,68,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2159

theorem m3248_136 : Upper (D 10) (R 10) [48,68,384,96,136] 13 :=
  permutation_upper _ _ _ [34,68,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2192

theorem m3248_160 : Upper (D 10) (R 10) [48,68,384,96,160] 13 :=
  permutation_upper _ _ _ [34,96,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2298

theorem m3248_384 : Upper (D 10) (R 10) [48,68,384,96,384] 13 :=
  permutation_upper _ _ _ [34,192,192,260,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2363

def r3248 : Route 9 := (fun mask => match mask with | 257 => (129,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 258 => (130,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 264 => (136,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | 288 => (160,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c3248 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 6 => 2 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3248 : Upper (D 10) (R 10) [48,68,384,96] 13 := by
  apply FastRouting.sound _ _ [48,68,384,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160,384] r3248 c3248
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3248_3
  · exact m3248_9
  · exact m3248_10
  · exact m3248_33
  · exact m3248_34
  · exact m3248_40
  · exact m3248_129
  · exact m3248_130
  · exact m3248_136
  · exact m3248_160
  · exact m3248_384

theorem m3249_3 : Upper (D 10) (R 10) [48,68,384,160,3] 13 :=
  permutation_upper _ _ _ [6,33,72,384,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1238

theorem m3249_9 : Upper (D 10) (R 10) [48,68,384,160,9] 13 :=
  permutation_upper _ _ _ [6,33,96,144,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1252

theorem m3249_10 : Upper (D 10) (R 10) [48,68,384,160,10] 13 :=
  permutation_upper _ _ _ [6,72,160,384,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1661

theorem m3249_33 : Upper (D 10) (R 10) [48,68,384,160,33] 13 :=
  permutation_upper _ _ _ [34,33,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1855

theorem m3249_34 : Upper (D 10) (R 10) [48,68,384,160,34] 13 :=
  permutation_upper _ _ _ [34,36,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1899

theorem m3249_40 : Upper (D 10) (R 10) [48,68,384,160,40] 13 :=
  permutation_upper _ _ _ [34,36,96,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1910

theorem m3249_65 : Upper (D 10) (R 10) [48,68,384,160,65] 13 :=
  permutation_upper _ _ _ [34,65,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1976

theorem m3249_66 : Upper (D 10) (R 10) [48,68,384,160,66] 13 :=
  permutation_upper _ _ _ [34,68,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2061

theorem m3249_72 : Upper (D 10) (R 10) [48,68,384,160,72] 13 :=
  permutation_upper _ _ _ [34,68,160,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2180

theorem m3249_96 : Upper (D 10) (R 10) [48,68,384,160,96] 13 :=
  permutation_upper _ _ _ [34,96,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2273

theorem m3249_257 : Upper (D 10) (R 10) [48,68,384,160,257] 13 :=
  permutation_upper _ _ _ [34,65,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2003

theorem m3249_258 : Upper (D 10) (R 10) [48,68,384,160,258] 13 :=
  permutation_upper _ _ _ [34,68,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2161

theorem m3249_264 : Upper (D 10) (R 10) [48,68,384,160,264] 13 :=
  permutation_upper _ _ _ [34,68,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2197

theorem m3249_288 : Upper (D 10) (R 10) [48,68,384,160,288] 13 :=
  permutation_upper _ _ _ [34,96,136,320,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2299

theorem m3249_320 : Upper (D 10) (R 10) [48,68,384,160,320] 13 :=
  permutation_upper _ _ _ [34,192,72,384,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2347

def r3249 : Route 9 := (fun mask => (mask,id))

def c3249 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 6 => 2 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u3249 : Upper (D 10) (R 10) [48,68,384,160] 13 := by
  apply FastRouting.sound _ _ [48,68,384,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,257,258,264,288,320] r3249 c3249
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3249_3
  · exact m3249_9
  · exact m3249_10
  · exact m3249_33
  · exact m3249_34
  · exact m3249_40
  · exact m3249_65
  · exact m3249_66
  · exact m3249_72
  · exact m3249_96
  · exact m3249_257
  · exact m3249_258
  · exact m3249_264
  · exact m3249_288
  · exact m3249_320

theorem m3250_3 : Upper (D 10) (R 10) [48,68,384,192,3] 13 :=
  permutation_upper _ _ _ [6,33,72,384,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1239

theorem m3250_9 : Upper (D 10) (R 10) [48,68,384,192,9] 13 :=
  permutation_upper _ _ _ [6,33,192,80,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1268

theorem m3250_10 : Upper (D 10) (R 10) [48,68,384,192,10] 13 :=
  permutation_upper _ _ _ [6,72,192,384,33] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1691

theorem m3250_33 : Upper (D 10) (R 10) [48,68,384,192,33] 13 :=
  permutation_upper _ _ _ [34,33,72,384,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1856

theorem m3250_34 : Upper (D 10) (R 10) [48,68,384,192,34] 13 :=
  permutation_upper _ _ _ [34,36,72,384,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1900

theorem m3250_40 : Upper (D 10) (R 10) [48,68,384,192,40] 13 :=
  permutation_upper _ _ _ [34,36,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1924

theorem m3250_257 : Upper (D 10) (R 10) [48,68,384,192,257] 13 :=
  permutation_upper _ _ _ [34,65,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2004

theorem m3250_258 : Upper (D 10) (R 10) [48,68,384,192,258] 13 :=
  permutation_upper _ _ _ [34,68,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2162

theorem m3250_264 : Upper (D 10) (R 10) [48,68,384,192,264] 13 :=
  permutation_upper _ _ _ [34,68,384,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2241

theorem m3250_288 : Upper (D 10) (R 10) [48,68,384,192,288] 13 :=
  permutation_upper _ _ _ [34,96,136,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2300

def r3250 : Route 9 := (fun mask => (mask,id))

def c3250 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 6 => 2 | 66 => 6 | 130 => 7 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3250 : Upper (D 10) (R 10) [48,68,384,192] 13 := by
  apply FastRouting.sound _ _ [48,68,384,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,257,258,264,288] r3250 c3250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3250_3
  · exact m3250_9
  · exact m3250_10
  · exact m3250_33
  · exact m3250_34
  · exact m3250_40
  · exact m3250_257
  · exact m3250_258
  · exact m3250_264
  · exact m3250_288

theorem m3251_3 : Upper (D 10) (R 10) [48,96,160,192,3] 13 :=
  permutation_upper _ _ _ [6,33,96,160,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1253

theorem m3251_5 : Upper (D 10) (R 10) [48,96,160,192,5] 13 :=
  permutation_upper _ _ _ [6,33,96,160,192] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1253

theorem m3251_6 : Upper (D 10) (R 10) [48,96,160,192,6] 13 :=
  permutation_upper _ _ _ [6,96,160,33,192] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1742

theorem m3251_9 : Upper (D 10) (R 10) [48,96,160,192,9] 13 :=
  permutation_upper _ _ _ [6,33,192,96,160] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1269

theorem m3251_10 : Upper (D 10) (R 10) [48,96,160,192,10] 13 :=
  permutation_upper _ _ _ [6,96,192,33,160] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1776

theorem m3251_12 : Upper (D 10) (R 10) [48,96,160,192,12] 13 :=
  permutation_upper _ _ _ [6,96,192,33,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1776

theorem m3251_257 : Upper (D 10) (R 10) [48,96,160,192,257] 13 :=
  permutation_upper _ _ _ [34,65,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2007

theorem m3251_258 : Upper (D 10) (R 10) [48,96,160,192,258] 13 :=
  permutation_upper _ _ _ [34,68,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2208

theorem m3251_260 : Upper (D 10) (R 10) [48,96,160,192,260] 13 :=
  permutation_upper _ _ _ [34,68,160,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2208

theorem m3251_264 : Upper (D 10) (R 10) [48,96,160,192,264] 13 :=
  permutation_upper _ _ _ [34,68,384,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2242

def r3251 : Route 9 := (fun mask => (mask,id))

def c3251 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 34 => 5 | 66 => 6 | 130 => 7 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3251 : Upper (D 10) (R 10) [48,96,160,192] 13 := by
  apply FastRouting.sound _ _ [48,96,160,192] 13 (by decide) (choices 2) [3,5,6,9,10,12,257,258,260,264] r3251 c3251
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3251_3
  · exact m3251_5
  · exact m3251_6
  · exact m3251_9
  · exact m3251_10
  · exact m3251_12
  · exact m3251_257
  · exact m3251_258
  · exact m3251_260
  · exact m3251_264

theorem m3252_3 : Upper (D 10) (R 10) [48,96,160,320,3] 13 :=
  permutation_upper _ _ _ [6,33,96,160,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1254

theorem m3252_5 : Upper (D 10) (R 10) [48,96,160,320,5] 13 :=
  permutation_upper _ _ _ [6,33,96,160,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1255

theorem m3252_6 : Upper (D 10) (R 10) [48,96,160,320,6] 13 :=
  permutation_upper _ _ _ [6,96,160,33,320] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1744

theorem m3252_9 : Upper (D 10) (R 10) [48,96,160,320,9] 13 :=
  permutation_upper _ _ _ [6,33,192,96,288] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1271

theorem m3252_10 : Upper (D 10) (R 10) [48,96,160,320,10] 13 :=
  permutation_upper _ _ _ [6,96,192,33,288] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1778

theorem m3252_12 : Upper (D 10) (R 10) [48,96,160,320,12] 13 :=
  permutation_upper _ _ _ [6,96,384,33,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1800

theorem m3252_129 : Upper (D 10) (R 10) [48,96,160,320,129] 13 :=
  permutation_upper _ _ _ [34,65,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1983

theorem m3252_130 : Upper (D 10) (R 10) [48,96,160,320,130] 13 :=
  permutation_upper _ _ _ [34,68,160,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2185

theorem m3252_132 : Upper (D 10) (R 10) [48,96,160,320,132] 13 :=
  permutation_upper _ _ _ [34,68,96,160,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2069

theorem m3252_136 : Upper (D 10) (R 10) [48,96,160,320,136] 13 :=
  permutation_upper _ _ _ [34,68,384,96,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2234

theorem m3252_257 : Upper (D 10) (R 10) [48,96,160,320,257] 13 :=
  permutation_upper _ _ _ [34,65,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2006

theorem m3252_258 : Upper (D 10) (R 10) [48,96,160,320,258] 13 :=
  permutation_upper _ _ _ [34,68,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2198

theorem m3252_260 : Upper (D 10) (R 10) [48,96,160,320,260] 13 :=
  permutation_upper _ _ _ [34,68,160,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2207

theorem m3252_264 : Upper (D 10) (R 10) [48,96,160,320,264] 13 :=
  permutation_upper _ _ _ [34,68,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2218

theorem m3252_384 : Upper (D 10) (R 10) [48,96,160,320,384] 13 :=
  permutation_upper _ _ _ [34,192,96,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2360

def r3252 : Route 9 := (fun mask => (mask,id))

def c3252 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 34 => 5 | 66 => 6 | 36 => 5 | 68 => 6 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u3252 : Upper (D 10) (R 10) [48,96,160,320] 13 := by
  apply FastRouting.sound _ _ [48,96,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,129,130,132,136,257,258,260,264,384] r3252 c3252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3252_3
  · exact m3252_5
  · exact m3252_6
  · exact m3252_9
  · exact m3252_10
  · exact m3252_12
  · exact m3252_129
  · exact m3252_130
  · exact m3252_132
  · exact m3252_136
  · exact m3252_257
  · exact m3252_258
  · exact m3252_260
  · exact m3252_264
  · exact m3252_384

theorem m3253_3 : Upper (D 10) (R 10) [48,96,192,384,3] 13 :=
  permutation_upper _ _ _ [6,33,96,192,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1256

theorem m3253_5 : Upper (D 10) (R 10) [48,96,192,384,5] 13 :=
  permutation_upper _ _ _ [6,33,192,96,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1272

theorem m3253_6 : Upper (D 10) (R 10) [48,96,192,384,6] 13 :=
  permutation_upper _ _ _ [6,96,192,33,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1779

theorem m3253_9 : Upper (D 10) (R 10) [48,96,192,384,9] 13 :=
  permutation_upper _ _ _ [6,33,192,288,320] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1279

theorem m3253_10 : Upper (D 10) (R 10) [48,96,192,384,10] 13 :=
  permutation_upper _ _ _ [6,96,384,33,192] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1801

theorem m3253_12 : Upper (D 10) (R 10) [48,96,192,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,33,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1834

theorem m3253_33 : Upper (D 10) (R 10) [48,96,192,384,33] 13 :=
  permutation_upper _ _ _ [34,33,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1857

theorem m3253_34 : Upper (D 10) (R 10) [48,96,192,384,34] 13 :=
  permutation_upper _ _ _ [34,36,96,192,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1911

theorem m3253_36 : Upper (D 10) (R 10) [48,96,192,384,36] 13 :=
  permutation_upper _ _ _ [34,36,192,96,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1927

theorem m3253_40 : Upper (D 10) (R 10) [48,96,192,384,40] 13 :=
  permutation_upper _ _ _ [34,36,192,288,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1930

theorem m3253_257 : Upper (D 10) (R 10) [48,96,192,384,257] 13 :=
  permutation_upper _ _ _ [34,65,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2008

theorem m3253_258 : Upper (D 10) (R 10) [48,96,192,384,258] 13 :=
  permutation_upper _ _ _ [34,68,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2209

theorem m3253_260 : Upper (D 10) (R 10) [48,96,192,384,260] 13 :=
  permutation_upper _ _ _ [34,68,384,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2243

theorem m3253_264 : Upper (D 10) (R 10) [48,96,192,384,264] 13 :=
  permutation_upper _ _ _ [34,68,192,288,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 7 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2221

theorem m3253_288 : Upper (D 10) (R 10) [48,96,192,384,288] 13 :=
  permutation_upper _ _ _ [34,96,160,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2301

def r3253 : Route 9 := (fun mask => (mask,id))

def c3253 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 66 => 6 | 130 => 7 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3253 : Upper (D 10) (R 10) [48,96,192,384] 13 := by
  apply FastRouting.sound _ _ [48,96,192,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,257,258,260,264,288] r3253 c3253
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3253_3
  · exact m3253_5
  · exact m3253_6
  · exact m3253_9
  · exact m3253_10
  · exact m3253_12
  · exact m3253_33
  · exact m3253_34
  · exact m3253_36
  · exact m3253_40
  · exact m3253_257
  · exact m3253_258
  · exact m3253_260
  · exact m3253_264
  · exact m3253_288

theorem m3254_3 : Upper (D 10) (R 10) [48,192,320,384,3] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1280

theorem m3254_5 : Upper (D 10) (R 10) [48,192,320,384,5] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1280

theorem m3254_6 : Upper (D 10) (R 10) [48,192,320,384,6] 13 :=
  permutation_upper _ _ _ [6,192,320,33,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 2 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1835

theorem m3254_9 : Upper (D 10) (R 10) [48,192,320,384,9] 13 :=
  permutation_upper _ _ _ [6,33,192,320,384] (fun i => match i.val with | 0 => 4 | 1 => 0 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 1 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1280

theorem m3254_10 : Upper (D 10) (R 10) [48,192,320,384,10] 13 :=
  permutation_upper _ _ _ [6,192,320,33,384] (fun i => match i.val with | 0 => 4 | 1 => 1 | 2 => 3 | 3 => 0 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 3 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1835

theorem m3254_12 : Upper (D 10) (R 10) [48,192,320,384,12] 13 :=
  permutation_upper _ _ _ [6,192,320,33,384] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1835

theorem m3254_33 : Upper (D 10) (R 10) [48,192,320,384,33] 13 :=
  permutation_upper _ _ _ [34,33,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1858

theorem m3254_34 : Upper (D 10) (R 10) [48,192,320,384,34] 13 :=
  permutation_upper _ _ _ [34,36,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1931

theorem m3254_36 : Upper (D 10) (R 10) [48,192,320,384,36] 13 :=
  permutation_upper _ _ _ [34,36,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1931

theorem m3254_40 : Upper (D 10) (R 10) [48,192,320,384,40] 13 :=
  permutation_upper _ _ _ [34,36,192,320,384] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1931

def r3254 : Route 9 := (fun mask => (mask,id))

def c3254 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u3254 : Upper (D 10) (R 10) [48,192,320,384] 13 := by
  apply FastRouting.sound _ _ [48,192,320,384] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r3254 c3254
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3254_3
  · exact m3254_5
  · exact m3254_6
  · exact m3254_9
  · exact m3254_10
  · exact m3254_12
  · exact m3254_33
  · exact m3254_34
  · exact m3254_36
  · exact m3254_40

def b3255 : PairBound 9 := { available := 432, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 140 268 432 432 496 432 432), lower := (rows 67 67 140 268 16 32 64 128 256), losses := [] }

theorem u3255 : Upper (D 10) (R 10) [66,65,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3255 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3256 : PairBound 9 := { available := 436, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 140 296 436 436 500 436 436), lower := (rows 67 67 140 296 16 32 64 128 256), losses := [] }

theorem u3256 : Upper (D 10) (R 10) [66,65,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3256 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3257 : PairBound 9 := { available := 444, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 164 296 444 444 508 444 444), lower := (rows 67 67 164 296 16 32 64 128 256), losses := [] }

theorem u3257 : Upper (D 10) (R 10) [66,65,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3257 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3258 : PairBound 9 := { available := 316, camps := [{ cop := 6, region := 3, targets := 160 }], pairs := [(0,5),(0,7)], upper := (rows 67 67 164 392 316 316 380 444 316), lower := (rows 67 67 164 392 16 32 64 128 256), losses := [] }

theorem u3258 : Upper (D 10) (R 10) [66,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3258 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3259 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 168 312 312 376 440 312), lower := (rows 67 70 133 168 16 32 64 128 256), losses := [] }

theorem u3259 : Upper (D 10) (R 10) [66,68,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3259 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3260 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 296 440 440 504 440 440), lower := (rows 67 70 133 296 16 32 64 128 256), losses := [] }

theorem u3260 : Upper (D 10) (R 10) [66,68,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3260 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3261 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 133 392 312 312 376 440 312), lower := (rows 67 70 133 392 16 32 64 128 256), losses := [] }

theorem u3261 : Upper (D 10) (R 10) [66,68,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3261 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3262 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 265 432 432 496 432 432), lower := (rows 67 70 140 265 16 32 64 128 256), losses := [] }

theorem u3262 : Upper (D 10) (R 10) [66,68,136,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3262 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3263 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 140 296 433 433 497 433 433), lower := (rows 67 70 140 296 16 32 64 128 256), losses := [] }

theorem u3263 : Upper (D 10) (R 10) [66,68,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3263 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3264 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 137 312 312 376 440 312), lower := (rows 67 70 164 137 16 32 64 128 256), losses := [] }

theorem u3264 : Upper (D 10) (R 10) [66,68,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3264 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3265 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 265 440 440 504 440 440), lower := (rows 67 70 164 265 16 32 64 128 256), losses := [] }

theorem u3265 : Upper (D 10) (R 10) [66,68,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3265 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3266 : PairBound 9 := { available := 441, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 296 441 441 505 441 441), lower := (rows 67 70 164 296 16 32 64 128 256), losses := [] }

theorem u3266 : Upper (D 10) (R 10) [66,68,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3266 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3267 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 164 392 313 313 377 441 313), lower := (rows 67 70 164 392 16 32 64 128 256), losses := [] }

theorem u3267 : Upper (D 10) (R 10) [66,68,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3267 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3268 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 137 312 312 376 440 312), lower := (rows 67 70 388 137 16 32 64 128 256), losses := [] }

theorem u3268 : Upper (D 10) (R 10) [66,68,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3268 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3269 : PairBound 9 := { available := 313, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 70 388 168 313 313 377 441 313), lower := (rows 67 70 388 168 16 32 64 128 256), losses := [] }

theorem u3269 : Upper (D 10) (R 10) [66,68,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3269 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3270 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 133 168 316 300 364 428 300), lower := (rows 67 82 133 168 16 32 64 128 256), losses := [] }

theorem u3270 : Upper (D 10) (R 10) [66,80,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3270 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3271 : PairBound 9 := { available := 424, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 133 268 440 424 488 424 424), lower := (rows 67 82 133 268 16 32 64 128 256), losses := [] }

theorem u3271 : Upper (D 10) (R 10) [66,80,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3271 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3272 : PairBound 9 := { available := 428, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 133 296 444 428 492 428 428), lower := (rows 67 82 133 296 16 32 64 128 256), losses := [] }

theorem u3272 : Upper (D 10) (R 10) [66,80,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3272 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3273 : PairBound 9 := { available := 300, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 133 392 316 300 364 428 300), lower := (rows 67 82 133 392 16 32 64 128 256), losses := [] }

theorem u3273 : Upper (D 10) (R 10) [66,80,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3273 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3274 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 140 268 433 417 481 417 417), lower := (rows 67 82 140 268 16 32 64 128 256), losses := [] }

theorem u3274 : Upper (D 10) (R 10) [66,80,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3274 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3275 : PairBound 9 := { available := 421, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 140 296 437 421 485 421 421), lower := (rows 67 82 140 296 16 32 64 128 256), losses := [] }

theorem u3275 : Upper (D 10) (R 10) [66,80,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3275 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3276 : PairBound 9 := { available := 429, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 164 296 445 429 493 429 429), lower := (rows 67 82 164 296 16 32 64 128 256), losses := [] }

theorem u3276 : Upper (D 10) (R 10) [66,80,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3276 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3277 : PairBound 9 := { available := 301, camps := [{ cop := 0, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 82 164 392 317 301 365 429 301), lower := (rows 67 82 164 392 16 32 64 128 256), losses := [] }

theorem u3277 : Upper (D 10) (R 10) [66,80,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3277 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3278 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 168 316 316 380 444 316), lower := (rows 67 98 133 168 16 32 64 128 256), losses := [] }

theorem u3278 : Upper (D 10) (R 10) [66,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3278 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3279 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 268 440 440 504 440 440), lower := (rows 67 98 133 268 16 32 64 128 256), losses := [] }

theorem u3279 : Upper (D 10) (R 10) [66,96,129,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3279 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3280 : PairBound 9 := { available := 444, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 296 444 444 508 444 444), lower := (rows 67 98 133 296 16 32 64 128 256), losses := [] }

theorem u3280 : Upper (D 10) (R 10) [66,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3280 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3281 : PairBound 9 := { available := 316, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 133 392 316 316 380 444 316), lower := (rows 67 98 133 392 16 32 64 128 256), losses := [] }

theorem u3281 : Upper (D 10) (R 10) [66,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3281 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3282 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 140 268 433 433 497 433 433), lower := (rows 67 98 140 268 16 32 64 128 256), losses := [] }

theorem u3282 : Upper (D 10) (R 10) [66,96,136,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3282 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3283 : PairBound 9 := { available := 437, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 140 296 437 437 501 437 437), lower := (rows 67 98 140 296 16 32 64 128 256), losses := [] }

theorem u3283 : Upper (D 10) (R 10) [66,96,136,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3283 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3284 : PairBound 9 := { available := 413, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 164 296 413 445 477 413 413), lower := (rows 67 98 164 296 16 32 64 128 256), losses := [] }

theorem u3284 : Upper (D 10) (R 10) [66,96,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3284 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3285 : PairBound 9 := { available := 317, camps := [{ cop := 0, region := 444, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 67 98 164 392 317 317 381 445 317), lower := (rows 67 98 164 392 16 32 64 128 256), losses := [] }

theorem u3285 : Upper (D 10) (R 10) [66,96,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3285 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3286 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 168 308 308 372 436 308), lower := (rows 67 131 76 168 16 32 64 128 256), losses := [] }

theorem u3286 : Upper (D 10) (R 10) [66,129,72,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3286 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3287 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 434, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 67 131 76 268 432 432 496 432 432), lower := (rows 67 131 76 268 16 32 64 128 256), losses := [] }

theorem u3287 : Upper (D 10) (R 10) [66,129,72,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3287 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3288 : PairBound 9 := { available := 436, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 296 436 436 500 436 436), lower := (rows 67 131 76 296 16 32 64 128 256), losses := [] }

theorem u3288 : Upper (D 10) (R 10) [66,129,72,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3288 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3289 : PairBound 9 := { available := 308, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 76 392 308 308 372 436 308), lower := (rows 67 131 76 392 16 32 64 128 256), losses := [] }

theorem u3289 : Upper (D 10) (R 10) [66,129,72,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3289 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3290 : PairBound 9 := { available := 424, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 84 268 440 424 488 424 424), lower := (rows 67 131 84 268 16 32 64 128 256), losses := [] }

theorem u3290 : Upper (D 10) (R 10) [66,129,80,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3290 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3291 : PairBound 9 := { available := 428, camps := [{ cop := 2, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 84 296 444 428 492 428 428), lower := (rows 67 131 84 296 16 32 64 128 256), losses := [] }

theorem u3291 : Upper (D 10) (R 10) [66,129,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3291 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3292 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 168 316 316 380 444 316), lower := (rows 67 131 100 168 16 32 64 128 256), losses := [] }

theorem u3292 : Upper (D 10) (R 10) [66,129,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3292 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3293 : PairBound 9 := { available := 440, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 268 440 440 504 440 440), lower := (rows 67 131 100 268 16 32 64 128 256), losses := [] }

theorem u3293 : Upper (D 10) (R 10) [66,129,96,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3293 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3294 : PairBound 9 := { available := 444, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 296 444 444 508 444 444), lower := (rows 67 131 100 296 16 32 64 128 256), losses := [] }

theorem u3294 : Upper (D 10) (R 10) [66,129,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3294 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3295 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 408, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 67 131 100 392 316 316 380 444 316), lower := (rows 67 131 100 392 16 32 64 128 256), losses := [] }

theorem u3295 : Upper (D 10) (R 10) [66,129,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3295 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3296 : PairBound 9 := { available := 312, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 131 196 268 312 312 376 440 312), lower := (rows 67 131 196 268 16 32 64 128 256), losses := [] }

theorem u3296 : Upper (D 10) (R 10) [66,129,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3296 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3297 : PairBound 9 := { available := 316, camps := [{ cop := 2, region := 3, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 67 131 196 296 316 316 380 444 316), lower := (rows 67 131 196 296 16 32 64 128 256), losses := [] }

theorem u3297 : Upper (D 10) (R 10) [66,129,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3297 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b3298 : PairBound 9 := { available := 180, camps := [{ cop := 2, region := 243, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 67 131 268 328 180 180 244 180 436), lower := (rows 67 131 268 328 16 32 64 128 256), losses := [] }

theorem u3298 : Upper (D 10) (R 10) [66,129,264,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b3298 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

theorem m3299_12 : Upper (D 10) (R 10) [66,129,272,288,12] 13 :=
  permutation_upper _ _ _ [6,65,96,144,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1446

theorem m3299_36 : Upper (D 10) (R 10) [66,129,272,288,36] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 3 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1981

theorem m3299_40 : Upper (D 10) (R 10) [66,129,272,288,40] 13 :=
  permutation_upper _ _ _ [34,96,65,144,264] (fun i => match i.val with | 0 => 4 | 1 => 3 | 2 => 2 | 3 => 0 | 4 => 1 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) (fun i => match i.val with | 0 => 3 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 0 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2256

theorem m3299_68 : Upper (D 10) (R 10) [66,129,272,288,68] 13 :=
  permutation_upper _ _ _ [66,129,72,260,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 0 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 2 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2403

theorem m3299_72 : Upper (D 10) (R 10) [66,129,272,288,72] 13 :=
  permutation_upper _ _ _ [66,129,72,288,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2406

theorem m3299_96 : Upper (D 10) (R 10) [66,129,272,288,96] 13 :=
  permutation_upper _ _ _ [66,129,96,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2411

theorem m3299_132 : Upper (D 10) (R 10) [66,129,272,288,132] 13 :=
  permutation_upper _ _ _ [66,129,72,260,160] (fun i => match i.val with | 0 => 4 | 1 => 2 | 2 => 1 | 3 => 0 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 8 | _ => 6) (fun i => match i.val with | 0 => 3 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 0 | 5 => 5 | 6 => 8 | 7 => 6 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2403

theorem m3299_136 : Upper (D 10) (R 10) [66,129,272,288,136] 13 :=
  permutation_upper _ _ _ [66,129,72,288,260] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2406

theorem m3299_160 : Upper (D 10) (R 10) [66,129,272,288,160] 13 :=
  permutation_upper _ _ _ [66,129,96,260,288] (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2411

theorem m3299_192 : Upper (D 10) (R 10) [66,129,272,288,192] 13 :=
  permutation_upper _ _ _ [66,129,192,260,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u2414

def r3299 : Route 9 := (fun mask => (mask,id))

def c3299 : Nat → Fin 9 := (fun mask => match mask with | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u3299 : Upper (D 10) (R 10) [66,129,272,288] 13 := by
  apply FastRouting.sound _ _ [66,129,272,288] 13 (by decide) (choices 2) [12,36,40,68,72,96,132,136,160,192] r3299 c3299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m3299_12
  · exact m3299_36
  · exact m3299_40
  · exact m3299_68
  · exact m3299_72
  · exact m3299_96
  · exact m3299_132
  · exact m3299_136
  · exact m3299_160
  · exact m3299_192

#print axioms u3299
end Delivery.IrregularNine14.P10
