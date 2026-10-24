import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0050
import IrregularNine14P03C0051
import IrregularNine14P03C0052
import IrregularNine14P03C0053
import IrregularNine14P03C0054
import IrregularNine14P03C0055
import IrregularNine14P03C0056
import IrregularNine14P03C0057

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b6180 : PairBound 9 := { available := 341, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 168 341 373 341 469 341), lower := (rows 35 67 140 168 16 32 64 128 256), losses := [] }

theorem u6180 : Upper (D 3) (R 3) [34,65,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6180
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6181 : PairBound 9 := { available := 309, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 200 309 309 373 437 309), lower := (rows 35 67 140 200 16 32 64 128 256), losses := [] }

theorem u6181 : Upper (D 3) (R 3) [34,65,136,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6181
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6182_5 : Upper (D 3) (R 3) [34,65,136,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3018

theorem m6182_33 : Upper (D 3) (R 3) [34,65,136,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3150

theorem m6182_36 : Upper (D 3) (R 3) [34,65,136,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3190

theorem m6182_65 : Upper (D 3) (R 3) [34,65,136,257,65] 13 :=
  permutation_upper _ _ _ [34,65,65,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3229

theorem m6182_68 : Upper (D 3) (R 3) [34,65,136,257,68] 13 :=
  permutation_upper _ _ _ [34,65,72,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3252

theorem m6182_96 : Upper (D 3) (R 3) [34,65,136,257,96] 13 :=
  permutation_upper _ _ _ [34,65,96,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3282

theorem m6182_129 : Upper (D 3) (R 3) [34,65,136,257,129] 13 :=
  permutation_upper _ _ _ [34,65,129,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3292

theorem m6182_132 : Upper (D 3) (R 3) [34,65,136,257,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3308

def r6182 : Route 9 := (fun mask => (mask,id))

def c6182 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6182 : Upper (D 3) (R 3) [34,65,136,257] 13 := by
  apply FastRouting.sound _ _ [34,65,136,257] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6182 c6182
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6182_5
  · exact m6182_33
  · exact m6182_36
  · exact m6182_65
  · exact m6182_68
  · exact m6182_96
  · exact m6182_129
  · exact m6182_132
  · exact u3318
  · exact u3319

theorem m6183_33 : Upper (D 3) (R 3) [34,65,136,260,33] 13 :=
  permutation_upper _ _ _ [34,65,33,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3152

theorem m6183_65 : Upper (D 3) (R 3) [34,65,136,260,65] 13 :=
  permutation_upper _ _ _ [34,65,65,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3231

theorem m6183_96 : Upper (D 3) (R 3) [34,65,136,260,96] 13 :=
  permutation_upper _ _ _ [34,65,96,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3284

theorem m6183_129 : Upper (D 3) (R 3) [34,65,136,260,129] 13 :=
  permutation_upper _ _ _ [34,65,129,144,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3294

def r6183 : Route 9 := (fun mask => (mask,id))

def c6183 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6183 : Upper (D 3) (R 3) [34,65,136,260] 13 := by
  apply FastRouting.sound _ _ [34,65,136,260] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6183 c6183
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6183_33
  · exact m6183_65
  · exact m6183_96
  · exact m6183_129
  · exact u3320
  · exact u3321

theorem m6184_5 : Upper (D 3) (R 3) [34,65,136,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3019

theorem m6184_33 : Upper (D 3) (R 3) [34,65,136,272,33] 13 :=
  permutation_upper _ _ _ [34,65,33,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3151

theorem m6184_36 : Upper (D 3) (R 3) [34,65,136,272,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3191

theorem m6184_65 : Upper (D 3) (R 3) [34,65,136,272,65] 13 :=
  permutation_upper _ _ _ [34,65,65,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3230

theorem m6184_68 : Upper (D 3) (R 3) [34,65,136,272,68] 13 :=
  permutation_upper _ _ _ [34,65,72,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3253

theorem m6184_96 : Upper (D 3) (R 3) [34,65,136,272,96] 13 :=
  permutation_upper _ _ _ [34,65,96,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3283

theorem m6184_129 : Upper (D 3) (R 3) [34,65,136,272,129] 13 :=
  permutation_upper _ _ _ [34,65,129,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3293

theorem m6184_132 : Upper (D 3) (R 3) [34,65,136,272,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3309

def r6184 : Route 9 := (fun mask => (mask,id))

def c6184 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6184 : Upper (D 3) (R 3) [34,65,136,272] 13 := by
  apply FastRouting.sound _ _ [34,65,136,272] 13 (by decide) (choices 2) [5,33,36,65,68,96,129,132,160,192] r6184 c6184
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6184_5
  · exact m6184_33
  · exact m6184_36
  · exact m6184_65
  · exact m6184_68
  · exact m6184_96
  · exact m6184_129
  · exact m6184_132
  · exact u3322
  · exact u3323

theorem m6185_5 : Upper (D 3) (R 3) [34,65,136,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3020

theorem m6185_65 : Upper (D 3) (R 3) [34,65,136,288,65] 13 :=
  permutation_upper _ _ _ [34,65,65,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3232

theorem m6185_68 : Upper (D 3) (R 3) [34,65,136,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3254

theorem m6185_129 : Upper (D 3) (R 3) [34,65,136,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3295

theorem m6185_132 : Upper (D 3) (R 3) [34,65,136,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3310

def r6185 : Route 9 := (fun mask => (mask,id))

def c6185 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6185 : Upper (D 3) (R 3) [34,65,136,288] 13 := by
  apply FastRouting.sound _ _ [34,65,136,288] 13 (by decide) (choices 2) [5,65,68,129,132,192] r6185 c6185
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6185_5
  · exact m6185_65
  · exact m6185_68
  · exact m6185_129
  · exact m6185_132
  · exact u3324

theorem m6186_5 : Upper (D 3) (R 3) [34,65,136,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3021

theorem m6186_33 : Upper (D 3) (R 3) [34,65,136,320,33] 13 :=
  permutation_upper _ _ _ [34,65,33,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3153

theorem m6186_36 : Upper (D 3) (R 3) [34,65,136,320,36] 13 :=
  permutation_upper _ _ _ [34,65,40,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3192

theorem m6186_129 : Upper (D 3) (R 3) [34,65,136,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3296

theorem m6186_132 : Upper (D 3) (R 3) [34,65,136,320,132] 13 :=
  permutation_upper _ _ _ [34,65,136,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3311

def r6186 : Route 9 := (fun mask => (mask,id))

def c6186 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6186 : Upper (D 3) (R 3) [34,65,136,320] 13 := by
  apply FastRouting.sound _ _ [34,65,136,320] 13 (by decide) (choices 2) [5,33,36,129,132,160] r6186 c6186
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6186_5
  · exact m6186_33
  · exact m6186_36
  · exact m6186_129
  · exact m6186_132
  · exact u3325

def b6187 : PairBound 9 := { available := 117, camps := [{ cop := 2, region := 115, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 140 392 117 117 117 245 373), lower := (rows 35 67 140 392 16 32 64 128 256), losses := [] }

theorem u6187 : Upper (D 3) (R 3) [34,65,136,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6187
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6188_5 : Upper (D 3) (R 3) [34,65,144,160,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3003

theorem m6188_9 : Upper (D 3) (R 3) [34,65,144,160,9] 13 :=
  permutation_upper _ _ _ [34,65,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3025

theorem m6188_12 : Upper (D 3) (R 3) [34,65,144,160,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3114

theorem m6188_65 : Upper (D 3) (R 3) [34,65,144,160,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3224

theorem m6188_68 : Upper (D 3) (R 3) [34,65,144,160,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3245

theorem m6188_72 : Upper (D 3) (R 3) [34,65,144,160,72] 13 :=
  permutation_upper _ _ _ [34,65,72,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3257

theorem m6188_257 : Upper (D 3) (R 3) [34,65,144,160,257] 13 :=
  permutation_upper _ _ _ [34,65,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3318

theorem m6188_260 : Upper (D 3) (R 3) [34,65,144,160,260] 13 :=
  permutation_upper _ _ _ [34,65,136,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3320

theorem m6188_264 : Upper (D 3) (R 3) [34,65,144,160,264] 13 :=
  permutation_upper _ _ _ [34,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3322

theorem m6188_320 : Upper (D 3) (R 3) [34,65,144,160,320] 13 :=
  permutation_upper _ _ _ [34,65,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3325

def r6188 : Route 9 := (fun mask => (mask,id))

def c6188 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6188 : Upper (D 3) (R 3) [34,65,144,160] 13 := by
  apply FastRouting.sound _ _ [34,65,144,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,257,260,264,320] r6188 c6188
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6188_5
  · exact m6188_9
  · exact m6188_12
  · exact m6188_65
  · exact m6188_68
  · exact m6188_72
  · exact m6188_257
  · exact m6188_260
  · exact m6188_264
  · exact m6188_320

theorem m6189_5 : Upper (D 3) (R 3) [34,65,144,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3004

theorem m6189_9 : Upper (D 3) (R 3) [34,65,144,192,9] 13 :=
  permutation_upper _ _ _ [34,65,9,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3033

theorem m6189_12 : Upper (D 3) (R 3) [34,65,144,192,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3115

theorem m6189_33 : Upper (D 3) (R 3) [34,65,144,192,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3145

theorem m6189_36 : Upper (D 3) (R 3) [34,65,144,192,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3181

theorem m6189_40 : Upper (D 3) (R 3) [34,65,144,192,40] 13 :=
  permutation_upper _ _ _ [34,65,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3195

theorem m6189_257 : Upper (D 3) (R 3) [34,65,144,192,257] 13 :=
  permutation_upper _ _ _ [34,65,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3319

theorem m6189_260 : Upper (D 3) (R 3) [34,65,144,192,260] 13 :=
  permutation_upper _ _ _ [34,65,136,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3321

theorem m6189_264 : Upper (D 3) (R 3) [34,65,144,192,264] 13 :=
  permutation_upper _ _ _ [34,65,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3323

theorem m6189_288 : Upper (D 3) (R 3) [34,65,144,192,288] 13 :=
  permutation_upper _ _ _ [34,65,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3324

def r6189 : Route 9 := (fun mask => (mask,id))

def c6189 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 72 => 6 | 136 => 7 | 96 => 6 | 160 => 7 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6189 : Upper (D 3) (R 3) [34,65,144,192] 13 := by
  apply FastRouting.sound _ _ [34,65,144,192] 13 (by decide) (choices 2) [5,9,12,33,36,40,257,260,264,288] r6189 c6189
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6189_5
  · exact m6189_9
  · exact m6189_12
  · exact m6189_33
  · exact m6189_36
  · exact m6189_40
  · exact m6189_257
  · exact m6189_260
  · exact m6189_264
  · exact m6189_288

theorem m6190_5 : Upper (D 3) (R 3) [34,65,144,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3005

theorem m6190_9 : Upper (D 3) (R 3) [34,65,144,257,9] 13 :=
  permutation_upper _ _ _ [34,65,9,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3041

theorem m6190_12 : Upper (D 3) (R 3) [34,65,144,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3116

theorem m6190_33 : Upper (D 3) (R 3) [34,65,144,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3146

theorem m6190_36 : Upper (D 3) (R 3) [34,65,144,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3182

theorem m6190_40 : Upper (D 3) (R 3) [34,65,144,257,40] 13 :=
  permutation_upper _ _ _ [34,65,40,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3202

theorem m6190_65 : Upper (D 3) (R 3) [34,65,144,257,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3225

theorem m6190_68 : Upper (D 3) (R 3) [34,65,144,257,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3246

theorem m6190_72 : Upper (D 3) (R 3) [34,65,144,257,72] 13 :=
  permutation_upper _ _ _ [34,65,72,257,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3262

theorem m6190_96 : Upper (D 3) (R 3) [34,65,144,257,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3279

theorem m6190_129 : Upper (D 3) (R 3) [34,65,144,257,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3288

theorem m6190_132 : Upper (D 3) (R 3) [34,65,144,257,132] 13 :=
  permutation_upper _ _ _ [34,65,136,132,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3305

theorem m6190_136 : Upper (D 3) (R 3) [34,65,144,257,136] 13 :=
  permutation_upper _ _ _ [34,65,136,144,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3308

theorem m6190_160 : Upper (D 3) (R 3) [34,65,144,257,160] 13 :=
  permutation_upper _ _ _ [34,65,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3312

theorem m6190_192 : Upper (D 3) (R 3) [34,65,144,257,192] 13 :=
  permutation_upper _ _ _ [34,65,136,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3315

def r6190 : Route 9 := (fun mask => (mask,id))

def c6190 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6190 : Upper (D 3) (R 3) [34,65,144,257] 13 := by
  apply FastRouting.sound _ _ [34,65,144,257] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96,129,132,136,160,192] r6190 c6190
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6190_5
  · exact m6190_9
  · exact m6190_12
  · exact m6190_33
  · exact m6190_36
  · exact m6190_40
  · exact m6190_65
  · exact m6190_68
  · exact m6190_72
  · exact m6190_96
  · exact m6190_129
  · exact m6190_132
  · exact m6190_136
  · exact m6190_160
  · exact m6190_192

theorem m6191_9 : Upper (D 3) (R 3) [34,65,144,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3056

theorem m6191_33 : Upper (D 3) (R 3) [34,65,144,260,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3147

theorem m6191_40 : Upper (D 3) (R 3) [34,65,144,260,40] 13 :=
  permutation_upper _ _ _ [34,65,40,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3209

theorem m6191_65 : Upper (D 3) (R 3) [34,65,144,260,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3226

theorem m6191_72 : Upper (D 3) (R 3) [34,65,144,260,72] 13 :=
  permutation_upper _ _ _ [34,65,72,272,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3267

theorem m6191_96 : Upper (D 3) (R 3) [34,65,144,260,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3280

theorem m6191_129 : Upper (D 3) (R 3) [34,65,144,260,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3289

theorem m6191_136 : Upper (D 3) (R 3) [34,65,144,260,136] 13 :=
  permutation_upper _ _ _ [34,65,136,144,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3309

theorem m6191_160 : Upper (D 3) (R 3) [34,65,144,260,160] 13 :=
  permutation_upper _ _ _ [34,65,136,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3313

theorem m6191_192 : Upper (D 3) (R 3) [34,65,144,260,192] 13 :=
  permutation_upper _ _ _ [34,65,136,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3316

def r6191 : Route 9 := (fun mask => (mask,id))

def c6191 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6191 : Upper (D 3) (R 3) [34,65,144,260] 13 := by
  apply FastRouting.sound _ _ [34,65,144,260] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r6191 c6191
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6191_9
  · exact m6191_33
  · exact m6191_40
  · exact m6191_65
  · exact m6191_72
  · exact m6191_96
  · exact m6191_129
  · exact m6191_136
  · exact m6191_160
  · exact m6191_192

theorem m6192_5 : Upper (D 3) (R 3) [34,65,144,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3006

theorem m6192_9 : Upper (D 3) (R 3) [34,65,144,288,9] 13 :=
  permutation_upper _ _ _ [34,65,9,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3061

theorem m6192_12 : Upper (D 3) (R 3) [34,65,144,288,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3117

theorem m6192_65 : Upper (D 3) (R 3) [34,65,144,288,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3227

theorem m6192_68 : Upper (D 3) (R 3) [34,65,144,288,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3247

theorem m6192_72 : Upper (D 3) (R 3) [34,65,144,288,72] 13 :=
  permutation_upper _ _ _ [34,65,72,288,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3270

theorem m6192_129 : Upper (D 3) (R 3) [34,65,144,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3290

theorem m6192_132 : Upper (D 3) (R 3) [34,65,144,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,132,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3306

theorem m6192_136 : Upper (D 3) (R 3) [34,65,144,288,136] 13 :=
  permutation_upper _ _ _ [34,65,136,144,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3310

theorem m6192_192 : Upper (D 3) (R 3) [34,65,144,288,192] 13 :=
  permutation_upper _ _ _ [34,65,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3317

def r6192 : Route 9 := (fun mask => (mask,id))

def c6192 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6192 : Upper (D 3) (R 3) [34,65,144,288] 13 := by
  apply FastRouting.sound _ _ [34,65,144,288] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6192 c6192
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6192_5
  · exact m6192_9
  · exact m6192_12
  · exact m6192_65
  · exact m6192_68
  · exact m6192_72
  · exact m6192_129
  · exact m6192_132
  · exact m6192_136
  · exact m6192_192

theorem m6193_5 : Upper (D 3) (R 3) [34,65,144,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3007

theorem m6193_9 : Upper (D 3) (R 3) [34,65,144,320,9] 13 :=
  permutation_upper _ _ _ [34,65,9,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3065

theorem m6193_12 : Upper (D 3) (R 3) [34,65,144,320,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3118

theorem m6193_33 : Upper (D 3) (R 3) [34,65,144,320,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3148

theorem m6193_36 : Upper (D 3) (R 3) [34,65,144,320,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3183

theorem m6193_40 : Upper (D 3) (R 3) [34,65,144,320,40] 13 :=
  permutation_upper _ _ _ [34,65,40,320,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3212

theorem m6193_129 : Upper (D 3) (R 3) [34,65,144,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3291

theorem m6193_132 : Upper (D 3) (R 3) [34,65,144,320,132] 13 :=
  permutation_upper _ _ _ [34,65,136,132,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3307

theorem m6193_136 : Upper (D 3) (R 3) [34,65,144,320,136] 13 :=
  permutation_upper _ _ _ [34,65,136,144,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3311

theorem m6193_160 : Upper (D 3) (R 3) [34,65,144,320,160] 13 :=
  permutation_upper _ _ _ [34,65,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3314

def r6193 : Route 9 := (fun mask => (mask,id))

def c6193 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6193 : Upper (D 3) (R 3) [34,65,144,320] 13 := by
  apply FastRouting.sound _ _ [34,65,144,320] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6193 c6193
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6193_5
  · exact m6193_9
  · exact m6193_12
  · exact m6193_33
  · exact m6193_36
  · exact m6193_40
  · exact m6193_129
  · exact m6193_132
  · exact m6193_136
  · exact m6193_160

theorem m6194_5 : Upper (D 3) (R 3) [34,65,144,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3008

theorem m6194_9 : Upper (D 3) (R 3) [34,65,144,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3073

theorem m6194_12 : Upper (D 3) (R 3) [34,65,144,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3119

theorem m6194_33 : Upper (D 3) (R 3) [34,65,144,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3149

theorem m6194_36 : Upper (D 3) (R 3) [34,65,144,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3184

theorem m6194_40 : Upper (D 3) (R 3) [34,65,144,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3216

theorem m6194_65 : Upper (D 3) (R 3) [34,65,144,384,65] 13 :=
  permutation_upper _ _ _ [34,65,65,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3228

theorem m6194_68 : Upper (D 3) (R 3) [34,65,144,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3248

theorem m6194_72 : Upper (D 3) (R 3) [34,65,144,384,72] 13 :=
  permutation_upper _ _ _ [34,65,72,384,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3272

theorem m6194_96 : Upper (D 3) (R 3) [34,65,144,384,96] 13 :=
  permutation_upper _ _ _ [34,65,96,132,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3281

def r6194 : Route 9 := (fun mask => (mask,id))

def c6194 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6194 : Upper (D 3) (R 3) [34,65,144,384] 13 := by
  apply FastRouting.sound _ _ [34,65,144,384] 13 (by decide) (choices 2) [5,9,12,33,36,40,65,68,72,96] r6194 c6194
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6194_5
  · exact m6194_9
  · exact m6194_12
  · exact m6194_33
  · exact m6194_36
  · exact m6194_40
  · exact m6194_65
  · exact m6194_68
  · exact m6194_72
  · exact m6194_96

theorem m6195_5 : Upper (D 3) (R 3) [34,65,160,192,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3026

theorem m6195_9 : Upper (D 3) (R 3) [34,65,160,192,9] 13 :=
  permutation_upper _ _ _ [34,65,9,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3034

theorem m6195_12 : Upper (D 3) (R 3) [34,65,160,192,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3120

def r6195 : Route 9 := (fun mask => (mask,id))

def c6195 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 40 => 5 | 72 => 6 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6195 : Upper (D 3) (R 3) [34,65,160,192] 13 := by
  apply FastRouting.sound _ _ [34,65,160,192] 13 (by decide) (choices 2) [5,9,12,257,260,264] r6195 c6195
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6195_5
  · exact m6195_9
  · exact m6195_12
  · exact u3326
  · exact u3327
  · exact u3328

theorem m6196_5 : Upper (D 3) (R 3) [34,65,160,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3027

theorem m6196_9 : Upper (D 3) (R 3) [34,65,160,257,9] 13 :=
  permutation_upper _ _ _ [34,65,9,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3042

theorem m6196_12 : Upper (D 3) (R 3) [34,65,160,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3121

theorem m6196_65 : Upper (D 3) (R 3) [34,65,160,257,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3233

theorem m6196_68 : Upper (D 3) (R 3) [34,65,160,257,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3258

theorem m6196_72 : Upper (D 3) (R 3) [34,65,160,257,72] 13 :=
  permutation_upper _ _ _ [34,65,72,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3263

theorem m6196_129 : Upper (D 3) (R 3) [34,65,160,257,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3297

theorem m6196_132 : Upper (D 3) (R 3) [34,65,160,257,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3312

theorem m6196_136 : Upper (D 3) (R 3) [34,65,160,257,136] 13 :=
  permutation_upper _ _ _ [34,65,136,257,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3318

theorem m6196_192 : Upper (D 3) (R 3) [34,65,160,257,192] 13 :=
  permutation_upper _ _ _ [34,65,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3326

def r6196 : Route 9 := (fun mask => (mask,id))

def c6196 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6196 : Upper (D 3) (R 3) [34,65,160,257] 13 := by
  apply FastRouting.sound _ _ [34,65,160,257] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6196 c6196
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6196_5
  · exact m6196_9
  · exact m6196_12
  · exact m6196_65
  · exact m6196_68
  · exact m6196_72
  · exact m6196_129
  · exact m6196_132
  · exact m6196_136
  · exact m6196_192

theorem m6197_9 : Upper (D 3) (R 3) [34,65,160,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3057

theorem m6197_65 : Upper (D 3) (R 3) [34,65,160,260,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3235

theorem m6197_72 : Upper (D 3) (R 3) [34,65,160,260,72] 13 :=
  permutation_upper _ _ _ [34,65,72,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3268

theorem m6197_129 : Upper (D 3) (R 3) [34,65,160,260,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3299

theorem m6197_136 : Upper (D 3) (R 3) [34,65,160,260,136] 13 :=
  permutation_upper _ _ _ [34,65,136,272,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3322

theorem m6197_192 : Upper (D 3) (R 3) [34,65,160,260,192] 13 :=
  permutation_upper _ _ _ [34,65,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3327

def r6197 : Route 9 := (fun mask => (mask,id))

def c6197 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6197 : Upper (D 3) (R 3) [34,65,160,260] 13 := by
  apply FastRouting.sound _ _ [34,65,160,260] 13 (by decide) (choices 2) [9,65,72,129,136,192] r6197 c6197
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6197_9
  · exact m6197_65
  · exact m6197_72
  · exact m6197_129
  · exact m6197_136
  · exact m6197_192

theorem m6198_5 : Upper (D 3) (R 3) [34,65,160,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3028

theorem m6198_9 : Upper (D 3) (R 3) [34,65,160,272,9] 13 :=
  permutation_upper _ _ _ [34,65,9,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3048

theorem m6198_12 : Upper (D 3) (R 3) [34,65,160,272,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3122

theorem m6198_65 : Upper (D 3) (R 3) [34,65,160,272,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3234

theorem m6198_68 : Upper (D 3) (R 3) [34,65,160,272,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3259

theorem m6198_72 : Upper (D 3) (R 3) [34,65,160,272,72] 13 :=
  permutation_upper _ _ _ [34,65,72,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3265

theorem m6198_129 : Upper (D 3) (R 3) [34,65,160,272,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3298

theorem m6198_132 : Upper (D 3) (R 3) [34,65,160,272,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3313

theorem m6198_136 : Upper (D 3) (R 3) [34,65,160,272,136] 13 :=
  permutation_upper _ _ _ [34,65,136,260,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3320

theorem m6198_192 : Upper (D 3) (R 3) [34,65,160,272,192] 13 :=
  permutation_upper _ _ _ [34,65,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3328

def r6198 : Route 9 := (fun mask => (mask,id))

def c6198 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6198 : Upper (D 3) (R 3) [34,65,160,272] 13 := by
  apply FastRouting.sound _ _ [34,65,160,272] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r6198 c6198
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6198_5
  · exact m6198_9
  · exact m6198_12
  · exact m6198_65
  · exact m6198_68
  · exact m6198_72
  · exact m6198_129
  · exact m6198_132
  · exact m6198_136
  · exact m6198_192

theorem m6199_5 : Upper (D 3) (R 3) [34,65,160,320,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3029

theorem m6199_9 : Upper (D 3) (R 3) [34,65,160,320,9] 13 :=
  permutation_upper _ _ _ [34,65,9,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3066

theorem m6199_12 : Upper (D 3) (R 3) [34,65,160,320,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3123

theorem m6199_129 : Upper (D 3) (R 3) [34,65,160,320,129] 13 :=
  permutation_upper _ _ _ [34,65,129,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3300

theorem m6199_132 : Upper (D 3) (R 3) [34,65,160,320,132] 13 :=
  permutation_upper _ _ _ [34,65,136,160,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3314

theorem m6199_136 : Upper (D 3) (R 3) [34,65,160,320,136] 13 :=
  permutation_upper _ _ _ [34,65,136,320,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3325

def r6199 : Route 9 := (fun mask => (mask,id))

def c6199 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6199 : Upper (D 3) (R 3) [34,65,160,320] 13 := by
  apply FastRouting.sound _ _ [34,65,160,320] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6199 c6199
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6199_5
  · exact m6199_9
  · exact m6199_12
  · exact m6199_129
  · exact m6199_132
  · exact m6199_136

theorem m6200_5 : Upper (D 3) (R 3) [34,65,160,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3030

theorem m6200_9 : Upper (D 3) (R 3) [34,65,160,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3074

theorem m6200_12 : Upper (D 3) (R 3) [34,65,160,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3124

theorem m6200_65 : Upper (D 3) (R 3) [34,65,160,384,65] 13 :=
  permutation_upper _ _ _ [34,65,65,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3236

theorem m6200_68 : Upper (D 3) (R 3) [34,65,160,384,68] 13 :=
  permutation_upper _ _ _ [34,65,72,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3260

theorem m6200_72 : Upper (D 3) (R 3) [34,65,160,384,72] 13 :=
  permutation_upper _ _ _ [34,65,72,384,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3273

def r6200 : Route 9 := (fun mask => (mask,id))

def c6200 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u6200 : Upper (D 3) (R 3) [34,65,160,384] 13 := by
  apply FastRouting.sound _ _ [34,65,160,384] 13 (by decide) (choices 2) [5,9,12,65,68,72] r6200 c6200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6200_5
  · exact m6200_9
  · exact m6200_12
  · exact m6200_65
  · exact m6200_68
  · exact m6200_72

theorem m6201_5 : Upper (D 3) (R 3) [34,65,192,257,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3035

theorem m6201_9 : Upper (D 3) (R 3) [34,65,192,257,9] 13 :=
  permutation_upper _ _ _ [34,65,9,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3043

theorem m6201_12 : Upper (D 3) (R 3) [34,65,192,257,12] 13 :=
  permutation_upper _ _ _ [34,65,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3125

theorem m6201_33 : Upper (D 3) (R 3) [34,65,192,257,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3154

theorem m6201_36 : Upper (D 3) (R 3) [34,65,192,257,36] 13 :=
  permutation_upper _ _ _ [34,65,40,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3196

theorem m6201_40 : Upper (D 3) (R 3) [34,65,192,257,40] 13 :=
  permutation_upper _ _ _ [34,65,40,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3203

theorem m6201_129 : Upper (D 3) (R 3) [34,65,192,257,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3301

theorem m6201_132 : Upper (D 3) (R 3) [34,65,192,257,132] 13 :=
  permutation_upper _ _ _ [34,65,136,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3315

theorem m6201_136 : Upper (D 3) (R 3) [34,65,192,257,136] 13 :=
  permutation_upper _ _ _ [34,65,136,257,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3319

theorem m6201_160 : Upper (D 3) (R 3) [34,65,192,257,160] 13 :=
  permutation_upper _ _ _ [34,65,160,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3326

def r6201 : Route 9 := (fun mask => (mask,id))

def c6201 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6201 : Upper (D 3) (R 3) [34,65,192,257] 13 := by
  apply FastRouting.sound _ _ [34,65,192,257] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6201 c6201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6201_5
  · exact m6201_9
  · exact m6201_12
  · exact m6201_33
  · exact m6201_36
  · exact m6201_40
  · exact m6201_129
  · exact m6201_132
  · exact m6201_136
  · exact m6201_160

theorem m6202_9 : Upper (D 3) (R 3) [34,65,192,260,9] 13 :=
  permutation_upper _ _ _ [34,65,9,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3058

theorem m6202_33 : Upper (D 3) (R 3) [34,65,192,260,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3156

theorem m6202_40 : Upper (D 3) (R 3) [34,65,192,260,40] 13 :=
  permutation_upper _ _ _ [34,65,40,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3210

theorem m6202_129 : Upper (D 3) (R 3) [34,65,192,260,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3303

theorem m6202_136 : Upper (D 3) (R 3) [34,65,192,260,136] 13 :=
  permutation_upper _ _ _ [34,65,136,272,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3323

theorem m6202_160 : Upper (D 3) (R 3) [34,65,192,260,160] 13 :=
  permutation_upper _ _ _ [34,65,160,192,264] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3328

def r6202 : Route 9 := (fun mask => (mask,id))

def c6202 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6202 : Upper (D 3) (R 3) [34,65,192,260] 13 := by
  apply FastRouting.sound _ _ [34,65,192,260] 13 (by decide) (choices 2) [9,33,40,129,136,160] r6202 c6202
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6202_9
  · exact m6202_33
  · exact m6202_40
  · exact m6202_129
  · exact m6202_136
  · exact m6202_160

theorem m6203_5 : Upper (D 3) (R 3) [34,65,192,272,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3036

theorem m6203_9 : Upper (D 3) (R 3) [34,65,192,272,9] 13 :=
  permutation_upper _ _ _ [34,65,9,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3049

theorem m6203_12 : Upper (D 3) (R 3) [34,65,192,272,12] 13 :=
  permutation_upper _ _ _ [34,65,24,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3126

theorem m6203_33 : Upper (D 3) (R 3) [34,65,192,272,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3155

theorem m6203_36 : Upper (D 3) (R 3) [34,65,192,272,36] 13 :=
  permutation_upper _ _ _ [34,65,40,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3197

theorem m6203_40 : Upper (D 3) (R 3) [34,65,192,272,40] 13 :=
  permutation_upper _ _ _ [34,65,40,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3205

theorem m6203_129 : Upper (D 3) (R 3) [34,65,192,272,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3302

theorem m6203_132 : Upper (D 3) (R 3) [34,65,192,272,132] 13 :=
  permutation_upper _ _ _ [34,65,136,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3316

theorem m6203_136 : Upper (D 3) (R 3) [34,65,192,272,136] 13 :=
  permutation_upper _ _ _ [34,65,136,260,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3321

theorem m6203_160 : Upper (D 3) (R 3) [34,65,192,272,160] 13 :=
  permutation_upper _ _ _ [34,65,160,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3327

def r6203 : Route 9 := (fun mask => (mask,id))

def c6203 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 260 => 8 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6203 : Upper (D 3) (R 3) [34,65,192,272] 13 := by
  apply FastRouting.sound _ _ [34,65,192,272] 13 (by decide) (choices 2) [5,9,12,33,36,40,129,132,136,160] r6203 c6203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6203_5
  · exact m6203_9
  · exact m6203_12
  · exact m6203_33
  · exact m6203_36
  · exact m6203_40
  · exact m6203_129
  · exact m6203_132
  · exact m6203_136
  · exact m6203_160

theorem m6204_5 : Upper (D 3) (R 3) [34,65,192,288,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3037

theorem m6204_9 : Upper (D 3) (R 3) [34,65,192,288,9] 13 :=
  permutation_upper _ _ _ [34,65,9,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3062

theorem m6204_12 : Upper (D 3) (R 3) [34,65,192,288,12] 13 :=
  permutation_upper _ _ _ [34,65,24,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3127

theorem m6204_129 : Upper (D 3) (R 3) [34,65,192,288,129] 13 :=
  permutation_upper _ _ _ [34,65,129,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3304

theorem m6204_132 : Upper (D 3) (R 3) [34,65,192,288,132] 13 :=
  permutation_upper _ _ _ [34,65,136,192,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3317

theorem m6204_136 : Upper (D 3) (R 3) [34,65,192,288,136] 13 :=
  permutation_upper _ _ _ [34,65,136,288,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3324

def r6204 : Route 9 := (fun mask => (mask,id))

def c6204 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u6204 : Upper (D 3) (R 3) [34,65,192,288] 13 := by
  apply FastRouting.sound _ _ [34,65,192,288] 13 (by decide) (choices 2) [5,9,12,129,132,136] r6204 c6204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6204_5
  · exact m6204_9
  · exact m6204_12
  · exact m6204_129
  · exact m6204_132
  · exact m6204_136

theorem m6205_5 : Upper (D 3) (R 3) [34,65,192,384,5] 13 :=
  permutation_upper _ _ _ [34,65,9,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3038

theorem m6205_9 : Upper (D 3) (R 3) [34,65,192,384,9] 13 :=
  permutation_upper _ _ _ [34,65,9,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3075

theorem m6205_12 : Upper (D 3) (R 3) [34,65,192,384,12] 13 :=
  permutation_upper _ _ _ [34,65,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3128

theorem m6205_33 : Upper (D 3) (R 3) [34,65,192,384,33] 13 :=
  permutation_upper _ _ _ [34,65,33,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3157

theorem m6205_36 : Upper (D 3) (R 3) [34,65,192,384,36] 13 :=
  permutation_upper _ _ _ [34,65,40,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3198

theorem m6205_40 : Upper (D 3) (R 3) [34,65,192,384,40] 13 :=
  permutation_upper _ _ _ [34,65,40,384,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3217

def r6205 : Route 9 := (fun mask => (mask,id))

def c6205 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 68 => 6 | 132 => 7 | 260 => 8 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 6 | 160 => 7 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u6205 : Upper (D 3) (R 3) [34,65,192,384] 13 := by
  apply FastRouting.sound _ _ [34,65,192,384] 13 (by decide) (choices 2) [5,9,12,33,36,40] r6205 c6205
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6205_5
  · exact m6205_9
  · exact m6205_12
  · exact m6205_33
  · exact m6205_36
  · exact m6205_40

def b6206 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 13 25 497 481 481 481 481), lower := (rows 35 70 13 25 16 32 64 128 256), losses := [] }

theorem u6206 : Upper (D 3) (R 3) [34,68,9,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6206
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6207 : PairBound 9 := { available := 465, camps := [{ cop := 0, region := 12, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 13 41 465 497 465 465 465), lower := (rows 35 70 13 41 16 32 64 128 256), losses := [] }

theorem u6207 : Upper (D 3) (R 3) [34,68,9,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6208 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 56 465 481 449 449 449), lower := (rows 35 70 13 56 16 32 64 128 256), losses := [] }

theorem u6208 : Upper (D 3) (R 3) [34,68,9,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6209 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 73 433 433 497 433 433), lower := (rows 35 70 13 73 16 32 64 128 256), losses := [] }

theorem u6209 : Upper (D 3) (R 3) [34,68,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6209
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6210 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 88 433 417 481 417 417), lower := (rows 35 70 13 88 16 32 64 128 256), losses := [] }

theorem u6210 : Upper (D 3) (R 3) [34,68,9,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6210
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6211 : PairBound 9 := { available := 401, camps := [{ cop := 3, region := 7, targets := 128 }], pairs := [(0,7)], upper := (rows 35 70 13 104 401 433 465 401 401), lower := (rows 35 70 13 104 16 32 64 128 256), losses := [] }

theorem u6211 : Upper (D 3) (R 3) [34,68,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6211
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6212 : PairBound 9 := { available := 497, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 13 137 497 497 497 497 497), lower := (rows 35 70 13 137 16 32 64 128 256), losses := [] }

theorem u6212 : Upper (D 3) (R 3) [34,68,9,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6212
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6213 : Route 9 := (fun mask => (mask,id))

def c6213 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6213 : Upper (D 3) (R 3) [34,68,9,144] 13 := by
  apply FastRouting.sound _ _ [34,68,9,144] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6213 c6213
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3329
  · exact u3330
  · exact u3331
  · exact u3332
  · exact u3333
  · exact u3334
  · exact u3335
  · exact u3336
  · exact u3337
  · exact u3338

def b6214 : PairBound 9 := { available := 465, camps := [{ cop := 2, region := 466, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 168 465 497 465 465 465), lower := (rows 35 70 13 168 16 32 64 128 256), losses := [] }

theorem u6214 : Upper (D 3) (R 3) [34,68,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6215 : PairBound 9 := { available := 433, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 200 433 433 497 433 433), lower := (rows 35 70 13 200 16 32 64 128 256), losses := [] }

theorem u6215 : Upper (D 3) (R 3) [34,68,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6216 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 35 70 13 265 241 241 241 241 497), lower := (rows 35 70 13 265 16 32 64 128 256), losses := [] }

theorem u6216 : Upper (D 3) (R 3) [34,68,9,257] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6217 : Route 9 := (fun mask => (mask,id))

def c6217 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6217 : Upper (D 3) (R 3) [34,68,9,272] 13 := by
  apply FastRouting.sound _ _ [34,68,9,272] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6217 c6217
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3339
  · exact u3340
  · exact u3341
  · exact u3342
  · exact u3343
  · exact u3344

def b6218 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 210, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 13 296 209 241 209 209 465), lower := (rows 35 70 13 296 16 32 64 128 256), losses := [] }

theorem u6218 : Upper (D 3) (R 3) [34,68,9,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6218
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6219 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 177, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 13 328 177 177 241 177 433), lower := (rows 35 70 13 328 16 32 64 128 256), losses := [] }

theorem u6219 : Upper (D 3) (R 3) [34,68,9,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6219
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r6220 : Route 9 := (fun mask => (mask,id))

def c6220 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6220 : Upper (D 3) (R 3) [34,68,9,384] 13 := by
  apply FastRouting.sound _ _ [34,68,9,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6220 c6220
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3345
  · exact u3346
  · exact u3347
  · exact u3348
  · exact u3349
  · exact u3350

def b6221 : PairBound 9 := { available := 449, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 28 41 465 481 449 449 449), lower := (rows 35 70 28 41 16 32 64 128 256), losses := [] }

theorem u6221 : Upper (D 3) (R 3) [34,68,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6221
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6222 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 73 433 417 481 417 417), lower := (rows 35 70 28 73 16 32 64 128 256), losses := [] }

theorem u6222 : Upper (D 3) (R 3) [34,68,24,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6222
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6223 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 104 401 417 449 385 385), lower := (rows 35 70 28 104 16 32 64 128 256), losses := [] }

theorem u6223 : Upper (D 3) (R 3) [34,68,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6223
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6224_33 : Upper (D 3) (R 3) [34,68,24,129,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3351

theorem m6224_65 : Upper (D 3) (R 3) [34,68,24,129,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3354

theorem m6224_96 : Upper (D 3) (R 3) [34,68,24,129,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3357

def r6224 : Route 9 := (fun mask => (mask,id))

def c6224 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u6224 : Upper (D 3) (R 3) [34,68,24,129] 13 := by
  apply FastRouting.sound _ _ [34,68,24,129] 13 (by decide) (choices 2) [33,65,96,129,160,192,257,288,320,384] r6224 c6224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6224_33
  · exact m6224_65
  · exact m6224_96
  · exact u3360
  · exact u3361
  · exact u3362
  · exact u3363
  · exact u3364
  · exact u3365
  · exact u3366

def b6225 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 464, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 28 168 465 481 449 449 449), lower := (rows 35 70 28 168 16 32 64 128 256), losses := [] }

theorem u6225 : Upper (D 3) (R 3) [34,68,24,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6225
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6226 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 200 433 417 481 417 417), lower := (rows 35 70 28 200 16 32 64 128 256), losses := [] }

theorem u6226 : Upper (D 3) (R 3) [34,68,24,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6226
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6227_33 : Upper (D 3) (R 3) [34,68,24,257,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3352

theorem m6227_65 : Upper (D 3) (R 3) [34,68,24,257,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3355

theorem m6227_96 : Upper (D 3) (R 3) [34,68,24,257,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3358

theorem m6227_129 : Upper (D 3) (R 3) [34,68,24,257,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3363

theorem m6227_160 : Upper (D 3) (R 3) [34,68,24,257,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3367

theorem m6227_192 : Upper (D 3) (R 3) [34,68,24,257,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3369

def r6227 : Route 9 := (fun mask => (mask,id))

def c6227 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6227 : Upper (D 3) (R 3) [34,68,24,257] 13 := by
  apply FastRouting.sound _ _ [34,68,24,257] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6227 c6227
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6227_33
  · exact m6227_65
  · exact m6227_96
  · exact m6227_129
  · exact m6227_160
  · exact m6227_192

def b6228 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 35 70 28 296 209 225 193 193 449), lower := (rows 35 70 28 296 16 32 64 128 256), losses := [] }

theorem u6228 : Upper (D 3) (R 3) [34,68,24,288] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b6229 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 161, targets := 64 }], pairs := [(0,6)], upper := (rows 35 70 28 328 177 161 225 161 417), lower := (rows 35 70 28 328 16 32 64 128 256), losses := [] }

theorem u6229 : Upper (D 3) (R 3) [34,68,24,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6229
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6230_33 : Upper (D 3) (R 3) [34,68,24,384,33] 13 :=
  permutation_upper _ _ _ [34,68,24,33,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3353

theorem m6230_65 : Upper (D 3) (R 3) [34,68,24,384,65] 13 :=
  permutation_upper _ _ _ [34,68,24,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3356

theorem m6230_96 : Upper (D 3) (R 3) [34,68,24,384,96] 13 :=
  permutation_upper _ _ _ [34,68,24,96,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3359

theorem m6230_129 : Upper (D 3) (R 3) [34,68,24,384,129] 13 :=
  permutation_upper _ _ _ [34,68,24,129,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3366

theorem m6230_160 : Upper (D 3) (R 3) [34,68,24,384,160] 13 :=
  permutation_upper _ _ _ [34,68,24,160,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3368

theorem m6230_192 : Upper (D 3) (R 3) [34,68,24,384,192] 13 :=
  permutation_upper _ _ _ [34,68,24,192,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3370

def r6230 : Route 9 := (fun mask => (mask,id))

def c6230 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u6230 : Upper (D 3) (R 3) [34,68,24,384] 13 := by
  apply FastRouting.sound _ _ [34,68,24,384] 13 (by decide) (choices 2) [33,65,96,129,160,192] r6230 c6230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6230_33
  · exact m6230_65
  · exact m6230_96
  · exact m6230_129
  · exact m6230_160
  · exact m6230_192

def r6231 : Route 9 := (fun mask => (mask,id))

def c6231 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u6231 : Upper (D 3) (R 3) [34,68,129,17] 13 := by
  apply FastRouting.sound _ _ [34,68,129,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192,257,264,288,320,384] r6231 c6231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u3371
  · exact u3372
  · exact u3373
  · exact u3374
  · exact u3375
  · exact u3376
  · exact u3377
  · exact u3378
  · exact u3379
  · exact u3380
  · exact u3381
  · exact u3382
  · exact u3383
  · exact u3384
  · exact u3385

def b6232 : PairBound 9 := { available := 473, camps := [{ cop := 3, region := 470, targets := 32 }], pairs := [(1,5)], upper := (rows 35 70 133 41 473 505 473 473 473), lower := (rows 35 70 133 41 16 32 64 128 256), losses := [] }

theorem u6232 : Upper (D 3) (R 3) [34,68,129,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6232
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6233_9 : Upper (D 3) (R 3) [34,68,129,48,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3373

def r6233 : Route 9 := (fun mask => (mask,id))

def c6233 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 96 => 5 | 160 => 5 | 288 => 5 | _ => 0)

theorem u6233 : Upper (D 3) (R 3) [34,68,129,48] 13 := by
  apply FastRouting.sound _ _ [34,68,129,48] 13 (by decide) (choices 2) [9,65,72,129,136,192,257,264,320,384] r6233 c6233
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6233_9
  · exact u3393
  · exact u3394
  · exact u3395
  · exact u3396
  · exact u3397
  · exact u3398
  · exact u3399
  · exact u3400
  · exact u3401

def b6234 : PairBound 9 := { available := 441, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6)], upper := (rows 35 70 133 73 441 441 505 441 441), lower := (rows 35 70 133 73 16 32 64 128 256), losses := [] }

theorem u6234 : Upper (D 3) (R 3) [34,68,129,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6234
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6235_9 : Upper (D 3) (R 3) [34,68,129,80,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3375

theorem m6235_33 : Upper (D 3) (R 3) [34,68,129,80,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3386

theorem m6235_40 : Upper (D 3) (R 3) [34,68,129,80,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3394

def r6235 : Route 9 := (fun mask => (mask,id))

def c6235 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6235 : Upper (D 3) (R 3) [34,68,129,80] 13 := by
  apply FastRouting.sound _ _ [34,68,129,80] 13 (by decide) (choices 2) [9,33,40,129,136,160,257,264,288,384] r6235 c6235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6235_9
  · exact m6235_33
  · exact m6235_40
  · exact u3408
  · exact u3409
  · exact u3410
  · exact u3411
  · exact u3412
  · exact u3413
  · exact u3414

theorem m6236_9 : Upper (D 3) (R 3) [34,68,129,96,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3376

def r6236 : Route 9 := (fun mask => (mask,id))

def c6236 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 65 => 6 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | _ => 0)

theorem u6236 : Upper (D 3) (R 3) [34,68,129,96] 13 := by
  apply FastRouting.sound _ _ [34,68,129,96] 13 (by decide) (choices 2) [9,129,136,257,264,384] r6236 c6236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6236_9
  · exact u3415
  · exact u3416
  · exact u3417
  · exact u3418
  · exact u3419

def b6237 : PairBound 9 := { available := 377, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 35 70 133 137 377 377 377 505 377), lower := (rows 35 70 133 137 16 32 64 128 256), losses := [] }

theorem u6237 : Upper (D 3) (R 3) [34,68,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b6237
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m6238_9 : Upper (D 3) (R 3) [34,68,129,144,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3378

theorem m6238_33 : Upper (D 3) (R 3) [34,68,129,144,33] 13 :=
  permutation_upper _ _ _ [34,68,129,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3387

theorem m6238_40 : Upper (D 3) (R 3) [34,68,129,144,40] 13 :=
  permutation_upper _ _ _ [34,68,129,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3396

theorem m6238_65 : Upper (D 3) (R 3) [34,68,129,144,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3402

theorem m6238_72 : Upper (D 3) (R 3) [34,68,129,144,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3409

theorem m6238_96 : Upper (D 3) (R 3) [34,68,129,144,96] 13 :=
  permutation_upper _ _ _ [34,68,129,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3416

def r6238 : Route 9 := (fun mask => (mask,id))

def c6238 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 136 => 7 | 160 => 7 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6238 : Upper (D 3) (R 3) [34,68,129,144] 13 := by
  apply FastRouting.sound _ _ [34,68,129,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,257,264,288,320] r6238 c6238
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6238_9
  · exact m6238_33
  · exact m6238_40
  · exact m6238_65
  · exact m6238_72
  · exact m6238_96
  · exact u3424
  · exact u3425
  · exact u3426
  · exact u3427

theorem m6239_9 : Upper (D 3) (R 3) [34,68,129,160,9] 13 :=
  permutation_upper _ _ _ [34,68,129,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3379

theorem m6239_65 : Upper (D 3) (R 3) [34,68,129,160,65] 13 :=
  permutation_upper _ _ _ [34,68,129,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3403

theorem m6239_72 : Upper (D 3) (R 3) [34,68,129,160,72] 13 :=
  permutation_upper _ _ _ [34,68,129,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u3410

def r6239 : Route 9 := (fun mask => (mask,id))

def c6239 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 129 => 7 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 384 => 7 | _ => 0)

theorem u6239 : Upper (D 3) (R 3) [34,68,129,160] 13 := by
  apply FastRouting.sound _ _ [34,68,129,160] 13 (by decide) (choices 2) [9,65,72,257,264,320] r6239 c6239
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m6239_9
  · exact m6239_65
  · exact m6239_72
  · exact u3428
  · exact u3429
  · exact u3430

#print axioms u6239
end Delivery.IrregularNine14.P03
