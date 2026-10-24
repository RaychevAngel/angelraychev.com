import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0219
import IrregularNine14P08C0221
import IrregularNine14P08C0222
import IrregularNine14P08C0223
import IrregularNine14P08C0224
import IrregularNine14P08C0225
import IrregularNine14P08C0226
import IrregularNine14P08C0227
import IrregularNine14P08C0235
import IrregularNine14P08C0236
import IrregularNine14P08C0237
import IrregularNine14P08C0240
import IrregularNine14P08C0244
import IrregularNine14P08C0245
import IrregularNine14P08C0246
import IrregularNine14P08C0247
import IrregularNine14P08C0248
import IrregularNine14P08C0249
import IrregularNine14P08C0250
import IrregularNine14P08C0251

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b21900 : PairBound 9 := { available := 105, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 266 121 105 105 233 361), lower := (rows 97 134 148 266 16 32 64 128 256), losses := [] }

theorem u21900 : Upper (D 8) (R 8) [96,132,144,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21900 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21901 : PairBound 9 := { available := 107, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 296 123 107 107 235 363), lower := (rows 97 134 148 296 16 32 64 128 256), losses := [] }

theorem u21901 : Upper (D 8) (R 8) [96,132,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21901 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21902 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 148 328 59 43 107 171 299), lower := (rows 97 134 148 328 16 32 64 128 256), losses := [] }

theorem u21902 : Upper (D 8) (R 8) [96,132,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21902 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21903 : PairBound 9 := { available := 123, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 265 123 123 123 251 379), lower := (rows 97 134 164 265 16 32 64 128 256), losses := [] }

theorem u21903 : Upper (D 8) (R 8) [96,132,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21903 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21904 : PairBound 9 := { available := 121, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 266 121 121 121 249 377), lower := (rows 97 134 164 266 16 32 64 128 256), losses := [] }

theorem u21904 : Upper (D 8) (R 8) [96,132,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21904 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21905 : PairBound 9 := { available := 91, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 296 91 123 91 219 347), lower := (rows 97 134 164 296 16 32 64 128 256), losses := [] }

theorem u21905 : Upper (D 8) (R 8) [96,132,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21905 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21906 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 164 328 59 59 123 187 315), lower := (rows 97 134 164 328 16 32 64 128 256), losses := [] }

theorem u21906 : Upper (D 8) (R 8) [96,132,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21906 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21907 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 196 265 59 59 123 187 315), lower := (rows 97 134 196 265 16 32 64 128 256), losses := [] }

theorem u21907 : Upper (D 8) (R 8) [96,132,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21907 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21908 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 196 266 57 57 121 185 313), lower := (rows 97 134 196 266 16 32 64 128 256), losses := [] }

theorem u21908 : Upper (D 8) (R 8) [96,132,192,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21908 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21909 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 377, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 196 296 59 59 123 187 315), lower := (rows 97 134 196 296 16 32 64 128 256), losses := [] }

theorem u21909 : Upper (D 8) (R 8) [96,132,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21909 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21910_3 : Upper (D 8) (R 8) [96,132,257,144,3] 13 :=
  permutation_upper _ _ _ [96,5,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13290

theorem m21910_9 : Upper (D 8) (R 8) [96,132,257,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13180

theorem m21910_10 : Upper (D 8) (R 8) [96,132,257,144,10] 13 :=
  permutation_upper _ _ _ [96,12,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14134

theorem m21910_33 : Upper (D 8) (R 8) [96,132,257,144,33] 13 :=
  permutation_upper _ _ _ [96,33,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14430

theorem m21910_34 : Upper (D 8) (R 8) [96,132,257,144,34] 13 :=
  permutation_upper _ _ _ [96,36,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14746

theorem m21910_40 : Upper (D 8) (R 8) [96,132,257,144,40] 13 :=
  permutation_upper _ _ _ [96,36,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14684

theorem m21910_65 : Upper (D 8) (R 8) [96,132,257,144,65] 13 :=
  permutation_upper _ _ _ [96,65,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14925

theorem m21910_66 : Upper (D 8) (R 8) [96,132,257,144,66] 13 :=
  permutation_upper _ _ _ [96,68,136,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14969

theorem m21910_72 : Upper (D 8) (R 8) [96,132,257,144,72] 13 :=
  permutation_upper _ _ _ [96,68,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14951

theorem m21910_96 : Upper (D 8) (R 8) [96,132,257,144,96] 13 :=
  permutation_upper _ _ _ [96,96,130,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15032

def r21910 : Route 9 := (fun mask => (mask,id))

def c21910 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21910 : Upper (D 8) (R 8) [96,132,257,144] 13 := by
  apply FastRouting.sound _ _ [96,132,257,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21910 c21910
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21910_3
  · exact m21910_9
  · exact m21910_10
  · exact m21910_33
  · exact m21910_34
  · exact m21910_40
  · exact m21910_65
  · exact m21910_66
  · exact m21910_72
  · exact m21910_96

theorem m21911_3 : Upper (D 8) (R 8) [96,132,257,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13291

theorem m21911_9 : Upper (D 8) (R 8) [96,132,257,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13408

theorem m21911_10 : Upper (D 8) (R 8) [96,132,257,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14164

theorem m21911_33 : Upper (D 8) (R 8) [96,132,257,160,33] 13 :=
  permutation_upper _ _ _ [96,33,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14441

theorem m21911_34 : Upper (D 8) (R 8) [96,132,257,160,34] 13 :=
  permutation_upper _ _ _ [96,36,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14747

theorem m21911_40 : Upper (D 8) (R 8) [96,132,257,160,40] 13 :=
  permutation_upper _ _ _ [96,36,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14787

theorem m21911_65 : Upper (D 8) (R 8) [96,132,257,160,65] 13 :=
  permutation_upper _ _ _ [96,65,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14931

theorem m21911_66 : Upper (D 8) (R 8) [96,132,257,160,66] 13 :=
  permutation_upper _ _ _ [96,68,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14970

theorem m21911_72 : Upper (D 8) (R 8) [96,132,257,160,72] 13 :=
  permutation_upper _ _ _ [96,68,160,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14986

theorem m21911_96 : Upper (D 8) (R 8) [96,132,257,160,96] 13 :=
  permutation_upper _ _ _ [96,96,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15037

def r21911 : Route 9 := (fun mask => (mask,id))

def c21911 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21911 : Upper (D 8) (R 8) [96,132,257,160] 13 := by
  apply FastRouting.sound _ _ [96,132,257,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21911 c21911
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21911_3
  · exact m21911_9
  · exact m21911_10
  · exact m21911_33
  · exact m21911_34
  · exact m21911_40
  · exact m21911_65
  · exact m21911_66
  · exact m21911_72
  · exact m21911_96

theorem m21912_3 : Upper (D 8) (R 8) [96,132,257,192,3] 13 :=
  permutation_upper _ _ _ [96,5,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13292

theorem m21912_9 : Upper (D 8) (R 8) [96,132,257,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13453

theorem m21912_10 : Upper (D 8) (R 8) [96,132,257,192,10] 13 :=
  permutation_upper _ _ _ [96,12,144,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14169

theorem m21912_33 : Upper (D 8) (R 8) [96,132,257,192,33] 13 :=
  permutation_upper _ _ _ [96,33,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14442

theorem m21912_34 : Upper (D 8) (R 8) [96,132,257,192,34] 13 :=
  permutation_upper _ _ _ [96,36,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14748

theorem m21912_40 : Upper (D 8) (R 8) [96,132,257,192,40] 13 :=
  permutation_upper _ _ _ [96,36,192,144,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14805

def r21912 : Route 9 := (fun mask => (mask,id))

def c21912 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21912 : Upper (D 8) (R 8) [96,132,257,192] 13 := by
  apply FastRouting.sound _ _ [96,132,257,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21912 c21912
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21912_3
  · exact m21912_9
  · exact m21912_10
  · exact m21912_33
  · exact m21912_34
  · exact m21912_40

def b21913 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 262 152 121 105 105 233 361), lower := (rows 97 134 262 152 16 32 64 128 256), losses := [] }

theorem u21913 : Upper (D 8) (R 8) [96,132,258,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21913 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21914 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 81, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 262 168 121 121 121 249 377), lower := (rows 97 134 262 168 16 32 64 128 256), losses := [] }

theorem u21914 : Upper (D 8) (R 8) [96,132,258,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21914 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21915 : PairBound 9 := { available := 57, camps := [{ cop := 3, region := 49, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 262 200 57 57 121 185 313), lower := (rows 97 134 262 200 16 32 64 128 256), losses := [] }

theorem u21915 : Upper (D 8) (R 8) [96,132,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21915 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21916 : PairBound 9 := { available := 99, camps := [{ cop := 1, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 268 152 115 99 99 227 355), lower := (rows 97 134 268 152 16 32 64 128 256), losses := [] }

theorem u21916 : Upper (D 8) (R 8) [96,132,264,144] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21916 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21917 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 268 168 115 115 115 243 371), lower := (rows 97 134 268 168 16 32 64 128 256), losses := [] }

theorem u21917 : Upper (D 8) (R 8) [96,132,264,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21917 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21918 : PairBound 9 := { available := 51, camps := [{ cop := 1, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 97 134 268 200 51 51 115 179 307), lower := (rows 97 134 268 200 16 32 64 128 256), losses := [] }

theorem u21918 : Upper (D 8) (R 8) [96,132,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21918 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21919_3 : Upper (D 8) (R 8) [96,132,272,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13297

theorem m21919_9 : Upper (D 8) (R 8) [96,132,272,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13409

theorem m21919_10 : Upper (D 8) (R 8) [96,132,272,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14165

theorem m21919_33 : Upper (D 8) (R 8) [96,132,272,160,33] 13 :=
  permutation_upper _ _ _ [96,33,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14443

theorem m21919_34 : Upper (D 8) (R 8) [96,132,272,160,34] 13 :=
  permutation_upper _ _ _ [96,36,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14752

theorem m21919_40 : Upper (D 8) (R 8) [96,132,272,160,40] 13 :=
  permutation_upper _ _ _ [96,36,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14788

theorem m21919_65 : Upper (D 8) (R 8) [96,132,272,160,65] 13 :=
  permutation_upper _ _ _ [96,65,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14932

theorem m21919_66 : Upper (D 8) (R 8) [96,132,272,160,66] 13 :=
  permutation_upper _ _ _ [96,68,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14972

theorem m21919_72 : Upper (D 8) (R 8) [96,132,272,160,72] 13 :=
  permutation_upper _ _ _ [96,68,160,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14987

theorem m21919_96 : Upper (D 8) (R 8) [96,132,272,160,96] 13 :=
  permutation_upper _ _ _ [96,96,136,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15038

def r21919 : Route 9 := (fun mask => (mask,id))

def c21919 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21919 : Upper (D 8) (R 8) [96,132,272,160] 13 := by
  apply FastRouting.sound _ _ [96,132,272,160] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21919 c21919
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21919_3
  · exact m21919_9
  · exact m21919_10
  · exact m21919_33
  · exact m21919_34
  · exact m21919_40
  · exact m21919_65
  · exact m21919_66
  · exact m21919_72
  · exact m21919_96

theorem m21920_3 : Upper (D 8) (R 8) [96,132,272,192,3] 13 :=
  permutation_upper _ _ _ [96,5,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13298

theorem m21920_9 : Upper (D 8) (R 8) [96,132,272,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13454

theorem m21920_10 : Upper (D 8) (R 8) [96,132,272,192,10] 13 :=
  permutation_upper _ _ _ [96,12,144,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14170

theorem m21920_33 : Upper (D 8) (R 8) [96,132,272,192,33] 13 :=
  permutation_upper _ _ _ [96,33,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14444

theorem m21920_34 : Upper (D 8) (R 8) [96,132,272,192,34] 13 :=
  permutation_upper _ _ _ [96,36,136,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14753

theorem m21920_40 : Upper (D 8) (R 8) [96,132,272,192,40] 13 :=
  permutation_upper _ _ _ [96,36,192,144,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14806

def r21920 : Route 9 := (fun mask => (mask,id))

def c21920 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21920 : Upper (D 8) (R 8) [96,132,272,192] 13 := by
  apply FastRouting.sound _ _ [96,132,272,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21920 c21920
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21920_3
  · exact m21920_9
  · exact m21920_10
  · exact m21920_33
  · exact m21920_34
  · exact m21920_40

theorem m21921_3 : Upper (D 8) (R 8) [96,132,288,144,3] 13 :=
  permutation_upper _ _ _ [96,5,136,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13314

theorem m21921_9 : Upper (D 8) (R 8) [96,132,288,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13182

theorem m21921_10 : Upper (D 8) (R 8) [96,132,288,144,10] 13 :=
  permutation_upper _ _ _ [96,12,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14135

theorem m21921_33 : Upper (D 8) (R 8) [96,132,288,144,33] 13 :=
  permutation_upper _ _ _ [96,33,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14431

theorem m21921_34 : Upper (D 8) (R 8) [96,132,288,144,34] 13 :=
  permutation_upper _ _ _ [96,36,136,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14764

theorem m21921_40 : Upper (D 8) (R 8) [96,132,288,144,40] 13 :=
  permutation_upper _ _ _ [96,36,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14686

theorem m21921_65 : Upper (D 8) (R 8) [96,132,288,144,65] 13 :=
  permutation_upper _ _ _ [96,65,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14926

theorem m21921_66 : Upper (D 8) (R 8) [96,132,288,144,66] 13 :=
  permutation_upper _ _ _ [96,68,136,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14977

theorem m21921_72 : Upper (D 8) (R 8) [96,132,288,144,72] 13 :=
  permutation_upper _ _ _ [96,68,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14953

theorem m21921_96 : Upper (D 8) (R 8) [96,132,288,144,96] 13 :=
  permutation_upper _ _ _ [96,96,130,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15033

def r21921 : Route 9 := (fun mask => (mask,id))

def c21921 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21921 : Upper (D 8) (R 8) [96,132,288,144] 13 := by
  apply FastRouting.sound _ _ [96,132,288,144] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21921 c21921
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21921_3
  · exact m21921_9
  · exact m21921_10
  · exact m21921_33
  · exact m21921_34
  · exact m21921_40
  · exact m21921_65
  · exact m21921_66
  · exact m21921_72
  · exact m21921_96

theorem m21922_3 : Upper (D 8) (R 8) [96,132,288,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13315

theorem m21922_9 : Upper (D 8) (R 8) [96,132,288,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13411

theorem m21922_10 : Upper (D 8) (R 8) [96,132,288,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14166

theorem m21922_65 : Upper (D 8) (R 8) [96,132,288,160,65] 13 :=
  permutation_upper _ _ _ [96,65,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14933

theorem m21922_66 : Upper (D 8) (R 8) [96,132,288,160,66] 13 :=
  permutation_upper _ _ _ [96,68,136,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14978

theorem m21922_72 : Upper (D 8) (R 8) [96,132,288,160,72] 13 :=
  permutation_upper _ _ _ [96,68,160,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14989

def r21922 : Route 9 := (fun mask => (mask,id))

def c21922 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21922 : Upper (D 8) (R 8) [96,132,288,160] 13 := by
  apply FastRouting.sound _ _ [96,132,288,160] 13 (by decide) (choices 2) [3,9,10,65,66,72] r21922 c21922
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21922_3
  · exact m21922_9
  · exact m21922_10
  · exact m21922_65
  · exact m21922_66
  · exact m21922_72

theorem m21923_3 : Upper (D 8) (R 8) [96,132,288,192,3] 13 :=
  permutation_upper _ _ _ [96,5,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13316

theorem m21923_9 : Upper (D 8) (R 8) [96,132,288,192,9] 13 :=
  permutation_upper _ _ _ [96,5,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13456

theorem m21923_10 : Upper (D 8) (R 8) [96,132,288,192,10] 13 :=
  permutation_upper _ _ _ [96,12,144,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14171

theorem m21923_33 : Upper (D 8) (R 8) [96,132,288,192,33] 13 :=
  permutation_upper _ _ _ [96,33,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14445

theorem m21923_34 : Upper (D 8) (R 8) [96,132,288,192,34] 13 :=
  permutation_upper _ _ _ [96,36,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14765

theorem m21923_40 : Upper (D 8) (R 8) [96,132,288,192,40] 13 :=
  permutation_upper _ _ _ [96,36,192,144,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14808

def r21923 : Route 9 := (fun mask => (mask,id))

def c21923 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21923 : Upper (D 8) (R 8) [96,132,288,192] 13 := by
  apply FastRouting.sound _ _ [96,132,288,192] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21923 c21923
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21923_3
  · exact m21923_9
  · exact m21923_10
  · exact m21923_33
  · exact m21923_34
  · exact m21923_40

theorem m21924_3 : Upper (D 8) (R 8) [96,132,320,144,3] 13 :=
  permutation_upper _ _ _ [96,5,136,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13319

theorem m21924_9 : Upper (D 8) (R 8) [96,132,320,144,9] 13 :=
  permutation_upper _ _ _ [96,5,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13183

theorem m21924_10 : Upper (D 8) (R 8) [96,132,320,144,10] 13 :=
  permutation_upper _ _ _ [96,12,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14136

theorem m21924_33 : Upper (D 8) (R 8) [96,132,320,144,33] 13 :=
  permutation_upper _ _ _ [96,33,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14432

theorem m21924_34 : Upper (D 8) (R 8) [96,132,320,144,34] 13 :=
  permutation_upper _ _ _ [96,36,136,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14767

theorem m21924_40 : Upper (D 8) (R 8) [96,132,320,144,40] 13 :=
  permutation_upper _ _ _ [96,36,130,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14687

def r21924 : Route 9 := (fun mask => (mask,id))

def c21924 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21924 : Upper (D 8) (R 8) [96,132,320,144] 13 := by
  apply FastRouting.sound _ _ [96,132,320,144] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21924 c21924
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21924_3
  · exact m21924_9
  · exact m21924_10
  · exact m21924_33
  · exact m21924_34
  · exact m21924_40

theorem m21925_3 : Upper (D 8) (R 8) [96,132,320,160,3] 13 :=
  permutation_upper _ _ _ [96,5,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13320

theorem m21925_9 : Upper (D 8) (R 8) [96,132,320,160,9] 13 :=
  permutation_upper _ _ _ [96,5,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13412

theorem m21925_10 : Upper (D 8) (R 8) [96,132,320,160,10] 13 :=
  permutation_upper _ _ _ [96,12,144,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14167

theorem m21925_33 : Upper (D 8) (R 8) [96,132,320,160,33] 13 :=
  permutation_upper _ _ _ [96,33,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14446

theorem m21925_34 : Upper (D 8) (R 8) [96,132,320,160,34] 13 :=
  permutation_upper _ _ _ [96,36,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14768

theorem m21925_40 : Upper (D 8) (R 8) [96,132,320,160,40] 13 :=
  permutation_upper _ _ _ [96,36,160,144,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14790

def r21925 : Route 9 := (fun mask => (mask,id))

def c21925 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21925 : Upper (D 8) (R 8) [96,132,320,160] 13 := by
  apply FastRouting.sound _ _ [96,132,320,160] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21925 c21925
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21925_3
  · exact m21925_9
  · exact m21925_10
  · exact m21925_33
  · exact m21925_34
  · exact m21925_40

theorem m21926_3 : Upper (D 8) (R 8) [96,144,160,257,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13184

theorem m21926_5 : Upper (D 8) (R 8) [96,144,160,257,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13404

theorem m21926_6 : Upper (D 8) (R 8) [96,144,160,257,6] 13 :=
  permutation_upper _ _ _ [96,12,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14137

theorem m21926_9 : Upper (D 8) (R 8) [96,144,160,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13477

theorem m21926_10 : Upper (D 8) (R 8) [96,144,160,257,10] 13 :=
  permutation_upper _ _ _ [96,12,130,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14146

theorem m21926_12 : Upper (D 8) (R 8) [96,144,160,257,12] 13 :=
  permutation_upper _ _ _ [96,12,160,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14217

theorem m21926_33 : Upper (D 8) (R 8) [96,144,160,257,33] 13 :=
  permutation_upper _ _ _ [96,33,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14433

theorem m21926_34 : Upper (D 8) (R 8) [96,144,160,257,34] 13 :=
  permutation_upper _ _ _ [96,36,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14688

theorem m21926_36 : Upper (D 8) (R 8) [96,144,160,257,36] 13 :=
  permutation_upper _ _ _ [96,36,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14784

theorem m21926_40 : Upper (D 8) (R 8) [96,144,160,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14830

theorem m21926_65 : Upper (D 8) (R 8) [96,144,160,257,65] 13 :=
  permutation_upper _ _ _ [96,65,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14927

theorem m21926_66 : Upper (D 8) (R 8) [96,144,160,257,66] 13 :=
  permutation_upper _ _ _ [96,68,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14954

theorem m21926_68 : Upper (D 8) (R 8) [96,144,160,257,68] 13 :=
  permutation_upper _ _ _ [96,68,160,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14983

theorem m21926_72 : Upper (D 8) (R 8) [96,144,160,257,72] 13 :=
  permutation_upper _ _ _ [96,68,257,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14997

theorem m21926_96 : Upper (D 8) (R 8) [96,144,160,257,96] 13 :=
  permutation_upper _ _ _ [96,96,130,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15034

def r21926 : Route 9 := (fun mask => (mask,id))

def c21926 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21926 : Upper (D 8) (R 8) [96,144,160,257] 13 := by
  apply FastRouting.sound _ _ [96,144,160,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,65,66,68,72,96] r21926 c21926
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21926_3
  · exact m21926_5
  · exact m21926_6
  · exact m21926_9
  · exact m21926_10
  · exact m21926_12
  · exact m21926_33
  · exact m21926_34
  · exact m21926_36
  · exact m21926_40
  · exact m21926_65
  · exact m21926_66
  · exact m21926_68
  · exact m21926_72
  · exact m21926_96

theorem m21927_5 : Upper (D 8) (R 8) [96,144,160,258,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13405

theorem m21927_9 : Upper (D 8) (R 8) [96,144,160,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13556

theorem m21927_12 : Upper (D 8) (R 8) [96,144,160,258,12] 13 :=
  permutation_upper _ _ _ [96,12,160,272,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14232

theorem m21927_33 : Upper (D 8) (R 8) [96,144,160,258,33] 13 :=
  permutation_upper _ _ _ [96,33,130,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14434

theorem m21927_36 : Upper (D 8) (R 8) [96,144,160,258,36] 13 :=
  permutation_upper _ _ _ [96,36,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14785

theorem m21927_40 : Upper (D 8) (R 8) [96,144,160,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14872

theorem m21927_65 : Upper (D 8) (R 8) [96,144,160,258,65] 13 :=
  permutation_upper _ _ _ [96,65,130,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14928

theorem m21927_68 : Upper (D 8) (R 8) [96,144,160,258,68] 13 :=
  permutation_upper _ _ _ [96,68,160,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14984

theorem m21927_72 : Upper (D 8) (R 8) [96,144,160,258,72] 13 :=
  permutation_upper _ _ _ [96,68,264,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15006

theorem m21927_96 : Upper (D 8) (R 8) [96,144,160,258,96] 13 :=
  permutation_upper _ _ _ [96,96,130,160,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15035

def r21927 : Route 9 := (fun mask => (mask,id))

def c21927 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21927 : Upper (D 8) (R 8) [96,144,160,258] 13 := by
  apply FastRouting.sound _ _ [96,144,160,258] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r21927 c21927
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21927_5
  · exact m21927_9
  · exact m21927_12
  · exact m21927_33
  · exact m21927_36
  · exact m21927_40
  · exact m21927_65
  · exact m21927_68
  · exact m21927_72
  · exact m21927_96

theorem m21928_3 : Upper (D 8) (R 8) [96,144,160,260,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13185

theorem m21928_9 : Upper (D 8) (R 8) [96,144,160,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13573

theorem m21928_10 : Upper (D 8) (R 8) [96,144,160,260,10] 13 :=
  permutation_upper _ _ _ [96,12,130,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14152

theorem m21928_33 : Upper (D 8) (R 8) [96,144,160,260,33] 13 :=
  permutation_upper _ _ _ [96,33,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14435

theorem m21928_34 : Upper (D 8) (R 8) [96,144,160,260,34] 13 :=
  permutation_upper _ _ _ [96,36,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14689

theorem m21928_40 : Upper (D 8) (R 8) [96,144,160,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14884

theorem m21928_65 : Upper (D 8) (R 8) [96,144,160,260,65] 13 :=
  permutation_upper _ _ _ [96,65,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14929

theorem m21928_66 : Upper (D 8) (R 8) [96,144,160,260,66] 13 :=
  permutation_upper _ _ _ [96,68,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14955

theorem m21928_72 : Upper (D 8) (R 8) [96,144,160,260,72] 13 :=
  permutation_upper _ _ _ [96,68,264,160,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15011

theorem m21928_96 : Upper (D 8) (R 8) [96,144,160,260,96] 13 :=
  permutation_upper _ _ _ [96,96,130,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15036

def r21928 : Route 9 := (fun mask => (mask,id))

def c21928 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 129 => 7 | 257 => 8 | 6 => 2 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21928 : Upper (D 8) (R 8) [96,144,160,260] 13 := by
  apply FastRouting.sound _ _ [96,144,160,260] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96] r21928 c21928
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21928_3
  · exact m21928_9
  · exact m21928_10
  · exact m21928_33
  · exact m21928_34
  · exact m21928_40
  · exact m21928_65
  · exact m21928_66
  · exact m21928_72
  · exact m21928_96

theorem m21929_3 : Upper (D 8) (R 8) [96,144,160,288,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13186

theorem m21929_5 : Upper (D 8) (R 8) [96,144,160,288,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13406

theorem m21929_6 : Upper (D 8) (R 8) [96,144,160,288,6] 13 :=
  permutation_upper _ _ _ [96,12,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14138

theorem m21929_9 : Upper (D 8) (R 8) [96,144,160,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13624

theorem m21929_10 : Upper (D 8) (R 8) [96,144,160,288,10] 13 :=
  permutation_upper _ _ _ [96,12,130,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14158

theorem m21929_12 : Upper (D 8) (R 8) [96,144,160,288,12] 13 :=
  permutation_upper _ _ _ [96,12,160,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14238

theorem m21929_65 : Upper (D 8) (R 8) [96,144,160,288,65] 13 :=
  permutation_upper _ _ _ [96,65,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14930

theorem m21929_66 : Upper (D 8) (R 8) [96,144,160,288,66] 13 :=
  permutation_upper _ _ _ [96,68,130,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14956

theorem m21929_68 : Upper (D 8) (R 8) [96,144,160,288,68] 13 :=
  permutation_upper _ _ _ [96,68,160,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14985

theorem m21929_72 : Upper (D 8) (R 8) [96,144,160,288,72] 13 :=
  permutation_upper _ _ _ [96,68,288,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15018

def r21929 : Route 9 := (fun mask => (mask,id))

def c21929 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u21929 : Upper (D 8) (R 8) [96,144,160,288] 13 := by
  apply FastRouting.sound _ _ [96,144,160,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r21929 c21929
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21929_3
  · exact m21929_5
  · exact m21929_6
  · exact m21929_9
  · exact m21929_10
  · exact m21929_12
  · exact m21929_65
  · exact m21929_66
  · exact m21929_68
  · exact m21929_72

theorem m21930_3 : Upper (D 8) (R 8) [96,144,160,320,3] 13 :=
  permutation_upper _ _ _ [96,5,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13187

theorem m21930_5 : Upper (D 8) (R 8) [96,144,160,320,5] 13 :=
  permutation_upper _ _ _ [96,5,160,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13407

theorem m21930_6 : Upper (D 8) (R 8) [96,144,160,320,6] 13 :=
  permutation_upper _ _ _ [96,12,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14139

theorem m21930_9 : Upper (D 8) (R 8) [96,144,160,320,9] 13 :=
  permutation_upper _ _ _ [96,5,320,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13642

theorem m21930_10 : Upper (D 8) (R 8) [96,144,160,320,10] 13 :=
  permutation_upper _ _ _ [96,12,130,320,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14161

theorem m21930_12 : Upper (D 8) (R 8) [96,144,160,320,12] 13 :=
  permutation_upper _ _ _ [96,12,160,320,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14243

theorem m21930_33 : Upper (D 8) (R 8) [96,144,160,320,33] 13 :=
  permutation_upper _ _ _ [96,33,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14436

theorem m21930_34 : Upper (D 8) (R 8) [96,144,160,320,34] 13 :=
  permutation_upper _ _ _ [96,36,130,160,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14690

theorem m21930_36 : Upper (D 8) (R 8) [96,144,160,320,36] 13 :=
  permutation_upper _ _ _ [96,36,160,130,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14786

theorem m21930_40 : Upper (D 8) (R 8) [96,144,160,320,40] 13 :=
  permutation_upper _ _ _ [96,36,320,130,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14901

def r21930 : Route 9 := (fun mask => (mask,id))

def c21930 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21930 : Upper (D 8) (R 8) [96,144,160,320] 13 := by
  apply FastRouting.sound _ _ [96,144,160,320] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21930 c21930
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21930_3
  · exact m21930_5
  · exact m21930_6
  · exact m21930_9
  · exact m21930_10
  · exact m21930_12
  · exact m21930_33
  · exact m21930_34
  · exact m21930_36
  · exact m21930_40

theorem m21931_3 : Upper (D 8) (R 8) [96,144,192,257,3] 13 :=
  permutation_upper _ _ _ [96,5,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13188

theorem m21931_5 : Upper (D 8) (R 8) [96,144,192,257,5] 13 :=
  permutation_upper _ _ _ [96,5,192,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13450

theorem m21931_6 : Upper (D 8) (R 8) [96,144,192,257,6] 13 :=
  permutation_upper _ _ _ [96,12,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14140

theorem m21931_9 : Upper (D 8) (R 8) [96,144,192,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13478

theorem m21931_10 : Upper (D 8) (R 8) [96,144,192,257,10] 13 :=
  permutation_upper _ _ _ [96,12,130,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14147

theorem m21931_12 : Upper (D 8) (R 8) [96,144,192,257,12] 13 :=
  permutation_upper _ _ _ [96,12,192,257,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14250

theorem m21931_33 : Upper (D 8) (R 8) [96,144,192,257,33] 13 :=
  permutation_upper _ _ _ [96,33,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14437

theorem m21931_34 : Upper (D 8) (R 8) [96,144,192,257,34] 13 :=
  permutation_upper _ _ _ [96,36,130,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14691

theorem m21931_36 : Upper (D 8) (R 8) [96,144,192,257,36] 13 :=
  permutation_upper _ _ _ [96,36,192,130,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14802

theorem m21931_40 : Upper (D 8) (R 8) [96,144,192,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14831

def r21931 : Route 9 := (fun mask => (mask,id))

def c21931 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21931 : Upper (D 8) (R 8) [96,144,192,257] 13 := by
  apply FastRouting.sound _ _ [96,144,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21931 c21931
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21931_3
  · exact m21931_5
  · exact m21931_6
  · exact m21931_9
  · exact m21931_10
  · exact m21931_12
  · exact m21931_33
  · exact m21931_34
  · exact m21931_36
  · exact m21931_40

theorem m21932_5 : Upper (D 8) (R 8) [96,144,192,258,5] 13 :=
  permutation_upper _ _ _ [96,5,192,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13451

theorem m21932_9 : Upper (D 8) (R 8) [96,144,192,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13557

theorem m21932_12 : Upper (D 8) (R 8) [96,144,192,258,12] 13 :=
  permutation_upper _ _ _ [96,12,192,272,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14257

theorem m21932_33 : Upper (D 8) (R 8) [96,144,192,258,33] 13 :=
  permutation_upper _ _ _ [96,33,130,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14438

theorem m21932_36 : Upper (D 8) (R 8) [96,144,192,258,36] 13 :=
  permutation_upper _ _ _ [96,36,192,130,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14803

theorem m21932_40 : Upper (D 8) (R 8) [96,144,192,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14873

def r21932 : Route 9 := (fun mask => (mask,id))

def c21932 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21932 : Upper (D 8) (R 8) [96,144,192,258] 13 := by
  apply FastRouting.sound _ _ [96,144,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r21932 c21932
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21932_5
  · exact m21932_9
  · exact m21932_12
  · exact m21932_33
  · exact m21932_36
  · exact m21932_40

theorem m21933_3 : Upper (D 8) (R 8) [96,144,192,260,3] 13 :=
  permutation_upper _ _ _ [96,5,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13189

theorem m21933_9 : Upper (D 8) (R 8) [96,144,192,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13578

theorem m21933_10 : Upper (D 8) (R 8) [96,144,192,260,10] 13 :=
  permutation_upper _ _ _ [96,12,130,272,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14153

theorem m21933_33 : Upper (D 8) (R 8) [96,144,192,260,33] 13 :=
  permutation_upper _ _ _ [96,33,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14439

theorem m21933_34 : Upper (D 8) (R 8) [96,144,192,260,34] 13 :=
  permutation_upper _ _ _ [96,36,130,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14692

theorem m21933_40 : Upper (D 8) (R 8) [96,144,192,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,192,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14887

def r21933 : Route 9 := (fun mask => (mask,id))

def c21933 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21933 : Upper (D 8) (R 8) [96,144,192,260] 13 := by
  apply FastRouting.sound _ _ [96,144,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21933 c21933
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21933_3
  · exact m21933_9
  · exact m21933_10
  · exact m21933_33
  · exact m21933_34
  · exact m21933_40

theorem m21934_3 : Upper (D 8) (R 8) [96,144,192,288,3] 13 :=
  permutation_upper _ _ _ [96,5,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13190

theorem m21934_5 : Upper (D 8) (R 8) [96,144,192,288,5] 13 :=
  permutation_upper _ _ _ [96,5,192,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13452

theorem m21934_6 : Upper (D 8) (R 8) [96,144,192,288,6] 13 :=
  permutation_upper _ _ _ [96,12,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14141

theorem m21934_9 : Upper (D 8) (R 8) [96,144,192,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13625

theorem m21934_10 : Upper (D 8) (R 8) [96,144,192,288,10] 13 :=
  permutation_upper _ _ _ [96,12,130,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14159

theorem m21934_12 : Upper (D 8) (R 8) [96,144,192,288,12] 13 :=
  permutation_upper _ _ _ [96,12,192,288,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14262

theorem m21934_33 : Upper (D 8) (R 8) [96,144,192,288,33] 13 :=
  permutation_upper _ _ _ [96,33,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14440

theorem m21934_34 : Upper (D 8) (R 8) [96,144,192,288,34] 13 :=
  permutation_upper _ _ _ [96,36,130,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14693

theorem m21934_36 : Upper (D 8) (R 8) [96,144,192,288,36] 13 :=
  permutation_upper _ _ _ [96,36,192,130,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14804

theorem m21934_40 : Upper (D 8) (R 8) [96,144,192,288,40] 13 :=
  permutation_upper _ _ _ [96,36,288,130,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14895

def r21934 : Route 9 := (fun mask => (mask,id))

def c21934 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21934 : Upper (D 8) (R 8) [96,144,192,288] 13 := by
  apply FastRouting.sound _ _ [96,144,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21934 c21934
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21934_3
  · exact m21934_5
  · exact m21934_6
  · exact m21934_9
  · exact m21934_10
  · exact m21934_12
  · exact m21934_33
  · exact m21934_34
  · exact m21934_36
  · exact m21934_40

def b21935 : PairBound 9 := { available := 95, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 162 164 265 95 127 95 223 351), lower := (rows 97 162 164 265 16 32 64 128 256), losses := [] }

theorem u21935 : Upper (D 8) (R 8) [96,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21935 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21936 : PairBound 9 := { available := 93, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 162 164 266 93 125 93 221 349), lower := (rows 97 162 164 266 16 32 64 128 256), losses := [] }

theorem u21936 : Upper (D 8) (R 8) [96,160,160,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21936 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21937 : PairBound 9 := { available := 31, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 97 162 164 328 31 63 95 159 287), lower := (rows 97 162 164 328 16 32 64 128 256), losses := [] }

theorem u21937 : Upper (D 8) (R 8) [96,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21937 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m21938_3 : Upper (D 8) (R 8) [96,160,192,257,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13417

theorem m21938_5 : Upper (D 8) (R 8) [96,160,192,257,5] 13 :=
  permutation_upper _ _ _ [96,5,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13457

theorem m21938_6 : Upper (D 8) (R 8) [96,160,192,257,6] 13 :=
  permutation_upper _ _ _ [96,12,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14208

theorem m21938_9 : Upper (D 8) (R 8) [96,160,192,257,9] 13 :=
  permutation_upper _ _ _ [96,5,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13479

theorem m21938_10 : Upper (D 8) (R 8) [96,160,192,257,10] 13 :=
  permutation_upper _ _ _ [96,12,160,257,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14219

theorem m21938_12 : Upper (D 8) (R 8) [96,160,192,257,12] 13 :=
  permutation_upper _ _ _ [96,12,192,257,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14251

theorem m21938_33 : Upper (D 8) (R 8) [96,160,192,257,33] 13 :=
  permutation_upper _ _ _ [96,33,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14447

theorem m21938_34 : Upper (D 8) (R 8) [96,160,192,257,34] 13 :=
  permutation_upper _ _ _ [96,36,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14791

theorem m21938_36 : Upper (D 8) (R 8) [96,160,192,257,36] 13 :=
  permutation_upper _ _ _ [96,36,192,160,257] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14809

theorem m21938_40 : Upper (D 8) (R 8) [96,160,192,257,40] 13 :=
  permutation_upper _ _ _ [96,36,257,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14835

def r21938 : Route 9 := (fun mask => (mask,id))

def c21938 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21938 : Upper (D 8) (R 8) [96,160,192,257] 13 := by
  apply FastRouting.sound _ _ [96,160,192,257] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21938 c21938
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21938_3
  · exact m21938_5
  · exact m21938_6
  · exact m21938_9
  · exact m21938_10
  · exact m21938_12
  · exact m21938_33
  · exact m21938_34
  · exact m21938_36
  · exact m21938_40

theorem m21939_5 : Upper (D 8) (R 8) [96,160,192,258,5] 13 :=
  permutation_upper _ _ _ [96,5,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13459

theorem m21939_9 : Upper (D 8) (R 8) [96,160,192,258,9] 13 :=
  permutation_upper _ _ _ [96,5,264,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13575

theorem m21939_12 : Upper (D 8) (R 8) [96,160,192,258,12] 13 :=
  permutation_upper _ _ _ [96,12,192,272,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14258

theorem m21939_33 : Upper (D 8) (R 8) [96,160,192,258,33] 13 :=
  permutation_upper _ _ _ [96,33,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14449

theorem m21939_36 : Upper (D 8) (R 8) [96,160,192,258,36] 13 :=
  permutation_upper _ _ _ [96,36,192,160,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14811

theorem m21939_40 : Upper (D 8) (R 8) [96,160,192,258,40] 13 :=
  permutation_upper _ _ _ [96,36,264,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14885

def r21939 : Route 9 := (fun mask => (mask,id))

def c21939 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21939 : Upper (D 8) (R 8) [96,160,192,258] 13 := by
  apply FastRouting.sound _ _ [96,160,192,258] 13 (by decide) (choices 2) [5,9,12,33,36,40] r21939 c21939
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21939_5
  · exact m21939_9
  · exact m21939_12
  · exact m21939_33
  · exact m21939_36
  · exact m21939_40

theorem m21940_3 : Upper (D 8) (R 8) [96,160,192,260,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13419

theorem m21940_9 : Upper (D 8) (R 8) [96,160,192,260,9] 13 :=
  permutation_upper _ _ _ [96,5,264,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13579

theorem m21940_10 : Upper (D 8) (R 8) [96,160,192,260,10] 13 :=
  permutation_upper _ _ _ [96,12,160,272,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14234

theorem m21940_33 : Upper (D 8) (R 8) [96,160,192,260,33] 13 :=
  permutation_upper _ _ _ [96,33,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14450

theorem m21940_34 : Upper (D 8) (R 8) [96,160,192,260,34] 13 :=
  permutation_upper _ _ _ [96,36,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14793

theorem m21940_40 : Upper (D 8) (R 8) [96,160,192,260,40] 13 :=
  permutation_upper _ _ _ [96,36,264,192,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14888

def r21940 : Route 9 := (fun mask => (mask,id))

def c21940 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21940 : Upper (D 8) (R 8) [96,160,192,260] 13 := by
  apply FastRouting.sound _ _ [96,160,192,260] 13 (by decide) (choices 2) [3,9,10,33,34,40] r21940 c21940
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21940_3
  · exact m21940_9
  · exact m21940_10
  · exact m21940_33
  · exact m21940_34
  · exact m21940_40

theorem m21941_3 : Upper (D 8) (R 8) [96,160,192,272,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13418

theorem m21941_5 : Upper (D 8) (R 8) [96,160,192,272,5] 13 :=
  permutation_upper _ _ _ [96,5,192,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13458

theorem m21941_6 : Upper (D 8) (R 8) [96,160,192,272,6] 13 :=
  permutation_upper _ _ _ [96,12,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14209

theorem m21941_9 : Upper (D 8) (R 8) [96,160,192,272,9] 13 :=
  permutation_upper _ _ _ [96,5,258,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13507

theorem m21941_10 : Upper (D 8) (R 8) [96,160,192,272,10] 13 :=
  permutation_upper _ _ _ [96,12,160,258,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14225

theorem m21941_12 : Upper (D 8) (R 8) [96,160,192,272,12] 13 :=
  permutation_upper _ _ _ [96,12,192,258,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14253

theorem m21941_33 : Upper (D 8) (R 8) [96,160,192,272,33] 13 :=
  permutation_upper _ _ _ [96,33,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14448

theorem m21941_34 : Upper (D 8) (R 8) [96,160,192,272,34] 13 :=
  permutation_upper _ _ _ [96,36,160,192,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14792

theorem m21941_36 : Upper (D 8) (R 8) [96,160,192,272,36] 13 :=
  permutation_upper _ _ _ [96,36,192,160,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14810

theorem m21941_40 : Upper (D 8) (R 8) [96,160,192,272,40] 13 :=
  permutation_upper _ _ _ [96,36,258,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14851

def r21941 : Route 9 := (fun mask => (mask,id))

def c21941 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 129 => 7 | 257 => 8 | 66 => 6 | 130 => 7 | 258 => 8 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21941 : Upper (D 8) (R 8) [96,160,192,272] 13 := by
  apply FastRouting.sound _ _ [96,160,192,272] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40] r21941 c21941
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21941_3
  · exact m21941_5
  · exact m21941_6
  · exact m21941_9
  · exact m21941_10
  · exact m21941_12
  · exact m21941_33
  · exact m21941_34
  · exact m21941_36
  · exact m21941_40

theorem m21942_3 : Upper (D 8) (R 8) [96,160,192,288,3] 13 :=
  permutation_upper _ _ _ [96,5,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13420

theorem m21942_5 : Upper (D 8) (R 8) [96,160,192,288,5] 13 :=
  permutation_upper _ _ _ [96,5,192,160,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 2 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13460

theorem m21942_6 : Upper (D 8) (R 8) [96,160,192,288,6] 13 :=
  permutation_upper _ _ _ [96,12,160,192,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14210

theorem m21942_9 : Upper (D 8) (R 8) [96,160,192,288,9] 13 :=
  permutation_upper _ _ _ [96,5,288,160,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u13629

theorem m21942_10 : Upper (D 8) (R 8) [96,160,192,288,10] 13 :=
  permutation_upper _ _ _ [96,12,160,288,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14239

theorem m21942_12 : Upper (D 8) (R 8) [96,160,192,288,12] 13 :=
  permutation_upper _ _ _ [96,12,192,288,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 2 | 3 => 3 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u14263

def r21942 : Route 9 := (fun mask => (mask,id))

def c21942 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u21942 : Upper (D 8) (R 8) [96,160,192,288] 13 := by
  apply FastRouting.sound _ _ [96,160,192,288] 13 (by decide) (choices 2) [3,5,6,9,10,12] r21942 c21942
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m21942_3
  · exact m21942_5
  · exact m21942_6
  · exact m21942_9
  · exact m21942_10
  · exact m21942_12

def b21943 : PairBound 9 := { available := 440, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 104 440 440 504 440 440), lower := (rows 193 7 7 104 16 32 64 128 256), losses := [] }

theorem u21943 : Upper (D 8) (R 8) [192,5,3,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21943 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21944 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 296 248 248 248 248 504), lower := (rows 193 7 7 296 16 32 64 128 256), losses := [] }

theorem u21944 : Upper (D 8) (R 8) [192,5,3,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21944 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21945 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 7 328 184 184 248 184 440), lower := (rows 193 7 7 328 16 32 64 128 256), losses := [] }

theorem u21945 : Upper (D 8) (R 8) [192,5,3,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21945 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21946 : PairBound 9 := { available := 480, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 26 496 480 480 480 480), lower := (rows 193 7 13 26 16 32 64 128 256), losses := [] }

theorem u21946 : Upper (D 8) (R 8) [192,5,9,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21946 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21947 : PairBound 9 := { available := 496, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 42 496 496 496 496 496), lower := (rows 193 7 13 42 16 32 64 128 256), losses := [] }

theorem u21947 : Upper (D 8) (R 8) [192,5,9,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21947 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21948 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 74 432 432 496 432 432), lower := (rows 193 7 13 74 16 32 64 128 256), losses := [] }

theorem u21948 : Upper (D 8) (R 8) [192,5,9,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21948 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21949 : PairBound 9 := { available := 434, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 104 434 434 498 434 434), lower := (rows 193 7 13 104 16 32 64 128 256), losses := [] }

theorem u21949 : Upper (D 8) (R 8) [192,5,9,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21949 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21950 : PairBound 9 := { available := 240, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 266 240 240 240 240 496), lower := (rows 193 7 13 266 16 32 64 128 256), losses := [] }

theorem u21950 : Upper (D 8) (R 8) [192,5,9,258] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21950 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21951 : PairBound 9 := { available := 242, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 13 296 242 242 242 242 498), lower := (rows 193 7 13 296 16 32 64 128 256), losses := [] }

theorem u21951 : Upper (D 8) (R 8) [192,5,9,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21951 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21952 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 13 328 178 178 242 178 434), lower := (rows 193 7 13 328 16 32 64 128 256), losses := [] }

theorem u21952 : Upper (D 8) (R 8) [192,5,9,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21952 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21953 : PairBound 9 := { available := 480, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 25 496 480 480 480 480), lower := (rows 193 7 14 25 16 32 64 128 256), losses := [] }

theorem u21953 : Upper (D 8) (R 8) [192,5,10,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21953 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21954 : PairBound 9 := { available := 496, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 41 496 496 496 496 496), lower := (rows 193 7 14 41 16 32 64 128 256), losses := [] }

theorem u21954 : Upper (D 8) (R 8) [192,5,10,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21954 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r21955 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c21955 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u21955 : Upper (D 8) (R 8) [192,5,10,48] 13 := by
  apply FastRouting.sound _ _ [192,5,10,48] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r21955 c21955
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u15088
  · exact u15089
  · exact u15090
  · exact u15091
  · exact u15092
  · exact u15093
  · exact u15094

def b21956 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 73 432 432 496 432 432), lower := (rows 193 7 14 73 16 32 64 128 256), losses := [] }

theorem u21956 : Upper (D 8) (R 8) [192,5,10,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21956 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21957 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 88 433 417 481 417 417), lower := (rows 193 7 14 88 16 32 64 128 256), losses := [] }

theorem u21957 : Upper (D 8) (R 8) [192,5,10,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21957 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21958 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 14 104 433 433 497 433 433), lower := (rows 193 7 14 104 16 32 64 128 256), losses := [] }

theorem u21958 : Upper (D 8) (R 8) [192,5,10,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21958 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b21959 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 14, targets := 32 }], pairs := [(1,5)], upper := (rows 193 7 14 200 305 305 369 433 305), lower := (rows 193 7 14 200 16 32 64 128 256), losses := [] }

theorem u21959 : Upper (D 8) (R 8) [192,5,10,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b21959 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u21959
end Delivery.IrregularNine14.P08
