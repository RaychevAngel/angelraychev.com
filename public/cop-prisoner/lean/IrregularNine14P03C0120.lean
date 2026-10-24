import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0087
import IrregularNine14P03C0088
import IrregularNine14P03C0089

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r7200 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7200 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7200 : Upper (D 3) (R 3) [258,96,9,132] 13 := by
  apply FastRouting.sound _ _ [258,96,9,132] 13 (by decide) (choices 2) [33,96,129,160] r7200 c7200
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5247
  · exact u5248
  · exact u5249
  · exact u5250

theorem m7201_5 : Upper (D 3) (R 3) [258,96,9,144,5] 13 :=
  permutation_upper _ _ _ [258,96,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5225

def r7201 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7201 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7201 : Upper (D 3) (R 3) [258,96,9,144] 13 := by
  apply FastRouting.sound _ _ [258,96,9,144] 13 (by decide) (choices 2) [5,33,36,96,129,132,160] r7201 c7201
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7201_5
  · exact u5251
  · exact u5252
  · exact u5253
  · exact u5254
  · exact u5255
  · exact u5256

def b7202 : PairBound 9 := { available := 213, camps := [{ cop := 2, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 259 98 13 168 213 245 213 213 469), lower := (rows 259 98 13 168 16 32 64 128 256), losses := [] }

theorem u7202 : Upper (D 3) (R 3) [258,96,9,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7202
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7203_9 : Upper (D 3) (R 3) [258,96,17,36,9] 13 :=
  permutation_upper _ _ _ [258,96,9,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5223

theorem m7203_65 : Upper (D 3) (R 3) [258,96,17,36,65] 13 :=
  permutation_upper _ _ _ [258,96,9,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5231

theorem m7203_72 : Upper (D 3) (R 3) [258,96,17,36,72] 13 :=
  permutation_upper _ _ _ [258,96,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5237

theorem m7203_129 : Upper (D 3) (R 3) [258,96,17,36,129] 13 :=
  permutation_upper _ _ _ [258,96,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5243

theorem m7203_136 : Upper (D 3) (R 3) [258,96,17,36,136] 13 :=
  permutation_upper _ _ _ [258,96,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5252

theorem m7203_192 : Upper (D 3) (R 3) [258,96,17,36,192] 13 :=
  permutation_upper _ _ _ [258,96,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5257

def r7203 : Route 9 := (fun mask => (mask,id))

def c7203 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7203 : Upper (D 3) (R 3) [258,96,17,36] 13 := by
  apply FastRouting.sound _ _ [258,96,17,36] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7203 c7203
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7203_9
  · exact m7203_65
  · exact m7203_72
  · exact m7203_129
  · exact m7203_136
  · exact m7203_192

theorem m7204_5 : Upper (D 3) (R 3) [258,96,17,129,5] 13 :=
  permutation_upper _ _ _ [258,96,9,5,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5221

theorem m7204_9 : Upper (D 3) (R 3) [258,96,17,129,9] 13 :=
  permutation_upper _ _ _ [258,96,9,17,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5224

theorem m7204_12 : Upper (D 3) (R 3) [258,96,17,129,12] 13 :=
  permutation_upper _ _ _ [258,96,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5229

theorem m7204_33 : Upper (D 3) (R 3) [258,96,17,129,33] 13 :=
  permutation_upper _ _ _ [258,96,9,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5232

theorem m7204_36 : Upper (D 3) (R 3) [258,96,17,129,36] 13 :=
  permutation_upper _ _ _ [258,96,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5235

theorem m7204_40 : Upper (D 3) (R 3) [258,96,17,129,40] 13 :=
  permutation_upper _ _ _ [258,96,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5238

theorem m7204_96 : Upper (D 3) (R 3) [258,96,17,129,96] 13 :=
  permutation_upper _ _ _ [258,96,9,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5241

theorem m7204_129 : Upper (D 3) (R 3) [258,96,17,129,129] 13 :=
  permutation_upper _ _ _ [258,96,9,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5244

theorem m7204_132 : Upper (D 3) (R 3) [258,96,17,129,132] 13 :=
  permutation_upper _ _ _ [258,96,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5249

theorem m7204_136 : Upper (D 3) (R 3) [258,96,17,129,136] 13 :=
  permutation_upper _ _ _ [258,96,9,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5254

theorem m7204_160 : Upper (D 3) (R 3) [258,96,17,129,160] 13 :=
  permutation_upper _ _ _ [258,96,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5258

def r7204 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7204 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7204 : Upper (D 3) (R 3) [258,96,17,129] 13 := by
  apply FastRouting.sound _ _ [258,96,17,129] 13 (by decide) (choices 2) [5,9,12,33,36,40,96,129,132,136,160] r7204 c7204
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7204_5
  · exact m7204_9
  · exact m7204_12
  · exact m7204_33
  · exact m7204_36
  · exact m7204_40
  · exact m7204_96
  · exact m7204_129
  · exact m7204_132
  · exact m7204_136
  · exact m7204_160

theorem m7205_9 : Upper (D 3) (R 3) [258,96,17,132,9] 13 :=
  permutation_upper _ _ _ [258,96,9,17,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5225

theorem m7205_33 : Upper (D 3) (R 3) [258,96,17,132,33] 13 :=
  permutation_upper _ _ _ [258,96,9,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5233

theorem m7205_40 : Upper (D 3) (R 3) [258,96,17,132,40] 13 :=
  permutation_upper _ _ _ [258,96,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5239

theorem m7205_96 : Upper (D 3) (R 3) [258,96,17,132,96] 13 :=
  permutation_upper _ _ _ [258,96,9,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5242

theorem m7205_129 : Upper (D 3) (R 3) [258,96,17,132,129] 13 :=
  permutation_upper _ _ _ [258,96,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5245

theorem m7205_136 : Upper (D 3) (R 3) [258,96,17,132,136] 13 :=
  permutation_upper _ _ _ [258,96,9,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5255

theorem m7205_160 : Upper (D 3) (R 3) [258,96,17,132,160] 13 :=
  permutation_upper _ _ _ [258,96,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5259

def r7205 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7205 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7205 : Upper (D 3) (R 3) [258,96,17,132] 13 := by
  apply FastRouting.sound _ _ [258,96,17,132] 13 (by decide) (choices 2) [9,33,40,96,129,136,160] r7205 c7205
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7205_9
  · exact m7205_33
  · exact m7205_40
  · exact m7205_96
  · exact m7205_129
  · exact m7205_136
  · exact m7205_160

theorem m7206_5 : Upper (D 3) (R 3) [258,96,17,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,5,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5222

theorem m7206_9 : Upper (D 3) (R 3) [258,96,17,160,9] 13 :=
  permutation_upper _ _ _ [258,96,9,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5226

theorem m7206_12 : Upper (D 3) (R 3) [258,96,17,160,12] 13 :=
  permutation_upper _ _ _ [258,96,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5230

theorem m7206_65 : Upper (D 3) (R 3) [258,96,17,160,65] 13 :=
  permutation_upper _ _ _ [258,96,9,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5234

theorem m7206_68 : Upper (D 3) (R 3) [258,96,17,160,68] 13 :=
  permutation_upper _ _ _ [258,96,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5236

theorem m7206_72 : Upper (D 3) (R 3) [258,96,17,160,72] 13 :=
  permutation_upper _ _ _ [258,96,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5240

theorem m7206_129 : Upper (D 3) (R 3) [258,96,17,160,129] 13 :=
  permutation_upper _ _ _ [258,96,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5246

theorem m7206_132 : Upper (D 3) (R 3) [258,96,17,160,132] 13 :=
  permutation_upper _ _ _ [258,96,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5250

theorem m7206_136 : Upper (D 3) (R 3) [258,96,17,160,136] 13 :=
  permutation_upper _ _ _ [258,96,9,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5256

theorem m7206_192 : Upper (D 3) (R 3) [258,96,17,160,192] 13 :=
  permutation_upper _ _ _ [258,96,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5260

def r7206 : Route 9 := (fun mask => (mask,id))

def c7206 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7206 : Upper (D 3) (R 3) [258,96,17,160] 13 := by
  apply FastRouting.sound _ _ [258,96,17,160] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7206 c7206
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7206_5
  · exact m7206_9
  · exact m7206_12
  · exact m7206_65
  · exact m7206_68
  · exact m7206_72
  · exact m7206_129
  · exact m7206_132
  · exact m7206_136
  · exact m7206_192

def b7207 : PairBound 9 := { available := 197, camps := [{ cop := 3, region := 212, targets := 32 }], pairs := [(2,5)], upper := (rows 259 98 28 41 213 229 197 197 453), lower := (rows 259 98 28 41 16 32 64 128 256), losses := [] }

theorem u7207 : Upper (D 3) (R 3) [258,96,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7207
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7208 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 385, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 28 44 209 225 193 193 449), lower := (rows 259 98 28 44 16 32 64 128 256), losses := [] }

theorem u7208 : Upper (D 3) (R 3) [258,96,24,36] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7208
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7209 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 28 104 149 165 197 133 389), lower := (rows 259 98 28 104 16 32 64 128 256), losses := [] }

theorem u7209 : Upper (D 3) (R 3) [258,96,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7209
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7210_5 : Upper (D 3) (R 3) [258,96,24,129,5] 13 :=
  permutation_upper _ _ _ [258,96,9,20,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5229

theorem m7210_33 : Upper (D 3) (R 3) [258,96,24,129,33] 13 :=
  permutation_upper _ _ _ [258,96,24,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5261

theorem m7210_36 : Upper (D 3) (R 3) [258,96,24,129,36] 13 :=
  permutation_upper _ _ _ [258,96,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5264

theorem m7210_96 : Upper (D 3) (R 3) [258,96,24,129,96] 13 :=
  permutation_upper _ _ _ [258,96,24,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5266

def r7210 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7210 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7210 : Upper (D 3) (R 3) [258,96,24,129] 13 := by
  apply FastRouting.sound _ _ [258,96,24,129] 13 (by decide) (choices 2) [5,33,36,96,129,132,160] r7210 c7210
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7210_5
  · exact m7210_33
  · exact m7210_36
  · exact m7210_96
  · exact u5268
  · exact u5269
  · exact u5270

theorem m7211_33 : Upper (D 3) (R 3) [258,96,24,132,33] 13 :=
  permutation_upper _ _ _ [258,96,24,33,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5262

theorem m7211_96 : Upper (D 3) (R 3) [258,96,24,132,96] 13 :=
  permutation_upper _ _ _ [258,96,24,96,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5267

theorem m7211_129 : Upper (D 3) (R 3) [258,96,24,132,129] 13 :=
  permutation_upper _ _ _ [258,96,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5269

def r7211 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 192 => (160,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7211 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7211 : Upper (D 3) (R 3) [258,96,24,132] 13 := by
  apply FastRouting.sound _ _ [258,96,24,132] 13 (by decide) (choices 2) [33,96,129,160] r7211 c7211
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7211_33
  · exact m7211_96
  · exact m7211_129
  · exact u5271

theorem m7212_5 : Upper (D 3) (R 3) [258,96,24,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,20,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5230

theorem m7212_65 : Upper (D 3) (R 3) [258,96,24,160,65] 13 :=
  permutation_upper _ _ _ [258,96,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5263

theorem m7212_68 : Upper (D 3) (R 3) [258,96,24,160,68] 13 :=
  permutation_upper _ _ _ [258,96,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5265

theorem m7212_129 : Upper (D 3) (R 3) [258,96,24,160,129] 13 :=
  permutation_upper _ _ _ [258,96,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5270

theorem m7212_132 : Upper (D 3) (R 3) [258,96,24,160,132] 13 :=
  permutation_upper _ _ _ [258,96,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5271

def r7212 : Route 9 := (fun mask => (mask,id))

def c7212 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7212 : Upper (D 3) (R 3) [258,96,24,160] 13 := by
  apply FastRouting.sound _ _ [258,96,24,160] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7212 c7212
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7212_5
  · exact m7212_65
  · exact m7212_68
  · exact m7212_129
  · exact m7212_132
  · exact u5272

def b7213 : PairBound 9 := { available := 153, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 76 153 185 217 153 409), lower := (rows 259 98 37 76 16 32 64 128 256), losses := [] }

theorem u7213 : Upper (D 3) (R 3) [258,96,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7213
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7214 : PairBound 9 := { available := 221, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 137 221 253 221 221 477), lower := (rows 259 98 37 137 16 32 64 128 256), losses := [] }

theorem u7214 : Upper (D 3) (R 3) [258,96,33,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7214
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7215 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 140 217 249 217 217 473), lower := (rows 259 98 37 140 16 32 64 128 256), losses := [] }

theorem u7215 : Upper (D 3) (R 3) [258,96,33,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7215
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7216 : PairBound 9 := { available := 157, camps := [{ cop := 2, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 37 200 157 189 221 157 413), lower := (rows 259 98 37 200 16 32 64 128 256), losses := [] }

theorem u7216 : Upper (D 3) (R 3) [258,96,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7216
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7217 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 44 76 145 177 209 145 401), lower := (rows 259 98 44 76 16 32 64 128 256), losses := [] }

theorem u7217 : Upper (D 3) (R 3) [258,96,40,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7217
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7218_5 : Upper (D 3) (R 3) [258,96,40,80,5] 13 :=
  permutation_upper _ _ _ [258,96,9,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5237

def r7218 : Route 9 := (fun mask => (mask,id))

def c7218 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7218 : Upper (D 3) (R 3) [258,96,40,80] 13 := by
  apply FastRouting.sound _ _ [258,96,40,80] 13 (by decide) (choices 2) [5,129,132] r7218 c7218
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7218_5
  · exact u5281
  · exact u5282

theorem m7219_5 : Upper (D 3) (R 3) [258,96,40,129,5] 13 :=
  permutation_upper _ _ _ [258,96,9,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5238

theorem m7219_65 : Upper (D 3) (R 3) [258,96,40,129,65] 13 :=
  permutation_upper _ _ _ [258,96,33,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5275

theorem m7219_68 : Upper (D 3) (R 3) [258,96,40,129,68] 13 :=
  permutation_upper _ _ _ [258,96,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5281

def r7219 : Route 9 := (fun mask => (mask,id))

def c7219 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7219 : Upper (D 3) (R 3) [258,96,40,129] 13 := by
  apply FastRouting.sound _ _ [258,96,40,129] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7219 c7219
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7219_5
  · exact m7219_65
  · exact m7219_68
  · exact u5283
  · exact u5284
  · exact u5285

def b7220 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 401, targets := 32 }], pairs := [(0,5)], upper := (rows 259 98 44 140 209 241 209 209 465), lower := (rows 259 98 44 140 16 32 64 128 256), losses := [] }

theorem u7220 : Upper (D 3) (R 3) [258,96,40,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7220
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7221_5 : Upper (D 3) (R 3) [258,96,40,144,5] 13 :=
  permutation_upper _ _ _ [258,96,9,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5239

theorem m7221_65 : Upper (D 3) (R 3) [258,96,40,144,65] 13 :=
  permutation_upper _ _ _ [258,96,33,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5276

theorem m7221_68 : Upper (D 3) (R 3) [258,96,40,144,68] 13 :=
  permutation_upper _ _ _ [258,96,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5282

def r7221 : Route 9 := (fun mask => (mask,id))

def c7221 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7221 : Upper (D 3) (R 3) [258,96,40,144] 13 := by
  apply FastRouting.sound _ _ [258,96,40,144] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7221 c7221
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7221_5
  · exact m7221_65
  · exact m7221_68
  · exact u5288
  · exact u5289
  · exact u5290

theorem m7222_5 : Upper (D 3) (R 3) [258,96,40,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5240

def r7222 : Route 9 := (fun mask => (mask,id))

def c7222 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7222 : Upper (D 3) (R 3) [258,96,40,192] 13 := by
  apply FastRouting.sound _ _ [258,96,40,192] 13 (by decide) (choices 2) [5,129,132] r7222 c7222
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7222_5
  · exact u5291
  · exact u5292

theorem m7223_5 : Upper (D 3) (R 3) [258,96,48,129,5] 13 :=
  permutation_upper _ _ _ [258,96,9,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5235

theorem m7223_9 : Upper (D 3) (R 3) [258,96,48,129,9] 13 :=
  permutation_upper _ _ _ [258,96,9,129,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5243

theorem m7223_12 : Upper (D 3) (R 3) [258,96,48,129,12] 13 :=
  permutation_upper _ _ _ [258,96,24,36,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5264

theorem m7223_65 : Upper (D 3) (R 3) [258,96,48,129,65] 13 :=
  permutation_upper _ _ _ [258,96,33,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5273

theorem m7223_68 : Upper (D 3) (R 3) [258,96,48,129,68] 13 :=
  permutation_upper _ _ _ [258,96,40,68,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5280

theorem m7223_72 : Upper (D 3) (R 3) [258,96,48,129,72] 13 :=
  permutation_upper _ _ _ [258,96,40,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5281

theorem m7223_129 : Upper (D 3) (R 3) [258,96,48,129,129] 13 :=
  permutation_upper _ _ _ [258,96,40,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5283

theorem m7223_132 : Upper (D 3) (R 3) [258,96,48,129,132] 13 :=
  permutation_upper _ _ _ [258,96,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5286

theorem m7223_136 : Upper (D 3) (R 3) [258,96,48,129,136] 13 :=
  permutation_upper _ _ _ [258,96,40,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5288

theorem m7223_192 : Upper (D 3) (R 3) [258,96,48,129,192] 13 :=
  permutation_upper _ _ _ [258,96,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5291

def r7223 : Route 9 := (fun mask => (mask,id))

def c7223 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7223 : Upper (D 3) (R 3) [258,96,48,129] 13 := by
  apply FastRouting.sound _ _ [258,96,48,129] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7223 c7223
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7223_5
  · exact m7223_9
  · exact m7223_12
  · exact m7223_65
  · exact m7223_68
  · exact m7223_72
  · exact m7223_129
  · exact m7223_132
  · exact m7223_136
  · exact m7223_192

theorem m7224_9 : Upper (D 3) (R 3) [258,96,48,132,9] 13 :=
  permutation_upper _ _ _ [258,96,9,144,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5252

theorem m7224_65 : Upper (D 3) (R 3) [258,96,48,132,65] 13 :=
  permutation_upper _ _ _ [258,96,33,68,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5274

theorem m7224_72 : Upper (D 3) (R 3) [258,96,48,132,72] 13 :=
  permutation_upper _ _ _ [258,96,40,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5282

theorem m7224_129 : Upper (D 3) (R 3) [258,96,48,132,129] 13 :=
  permutation_upper _ _ _ [258,96,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5284

theorem m7224_136 : Upper (D 3) (R 3) [258,96,48,132,136] 13 :=
  permutation_upper _ _ _ [258,96,40,144,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5289

theorem m7224_192 : Upper (D 3) (R 3) [258,96,48,132,192] 13 :=
  permutation_upper _ _ _ [258,96,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5292

def r7224 : Route 9 := (fun mask => (mask,id))

def c7224 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7224 : Upper (D 3) (R 3) [258,96,48,132] 13 := by
  apply FastRouting.sound _ _ [258,96,48,132] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7224 c7224
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7224_9
  · exact m7224_65
  · exact m7224_72
  · exact m7224_129
  · exact m7224_136
  · exact m7224_192

theorem m7225_5 : Upper (D 3) (R 3) [258,96,48,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5236

theorem m7225_9 : Upper (D 3) (R 3) [258,96,48,192,9] 13 :=
  permutation_upper _ _ _ [258,96,9,160,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5257

theorem m7225_12 : Upper (D 3) (R 3) [258,96,48,192,12] 13 :=
  permutation_upper _ _ _ [258,96,24,36,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5265

theorem m7225_129 : Upper (D 3) (R 3) [258,96,48,192,129] 13 :=
  permutation_upper _ _ _ [258,96,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5285

theorem m7225_132 : Upper (D 3) (R 3) [258,96,48,192,132] 13 :=
  permutation_upper _ _ _ [258,96,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5287

theorem m7225_136 : Upper (D 3) (R 3) [258,96,48,192,136] 13 :=
  permutation_upper _ _ _ [258,96,40,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5290

def r7225 : Route 9 := (fun mask => (mask,id))

def c7225 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 260 => 8 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7225 : Upper (D 3) (R 3) [258,96,48,192] 13 := by
  apply FastRouting.sound _ _ [258,96,48,192] 13 (by decide) (choices 2) [5,9,12,129,132,136] r7225 c7225
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7225_5
  · exact m7225_9
  · exact m7225_12
  · exact m7225_129
  · exact m7225_132
  · exact m7225_136

def b7226 : PairBound 9 := { available := 157, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 137 157 189 221 157 413), lower := (rows 259 98 100 137 16 32 64 128 256), losses := [] }

theorem u7226 : Upper (D 3) (R 3) [258,96,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7226
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7227 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 4, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 100 140 153 185 217 153 409), lower := (rows 259 98 100 140 16 32 64 128 256), losses := [] }

theorem u7227 : Upper (D 3) (R 3) [258,96,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7227
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7228 : PairBound 9 := { available := 125, camps := [{ cop := 2, region := 8, targets := 32 }], pairs := [(3,5)], upper := (rows 259 98 133 137 125 125 125 253 381), lower := (rows 259 98 133 137 16 32 64 128 256), losses := [] }

theorem u7228 : Upper (D 3) (R 3) [258,96,129,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7228
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7229 : PairBound 9 := { available := 121, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 259 98 133 140 121 121 121 249 377), lower := (rows 259 98 133 140 16 32 64 128 256), losses := [] }

theorem u7229 : Upper (D 3) (R 3) [258,96,129,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7229
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7230_5 : Upper (D 3) (R 3) [258,96,129,144,5] 13 :=
  permutation_upper _ _ _ [258,96,9,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5245

theorem m7230_9 : Upper (D 3) (R 3) [258,96,129,144,9] 13 :=
  permutation_upper _ _ _ [258,96,9,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5249

theorem m7230_12 : Upper (D 3) (R 3) [258,96,129,144,12] 13 :=
  permutation_upper _ _ _ [258,96,24,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5269

theorem m7230_33 : Upper (D 3) (R 3) [258,96,129,144,33] 13 :=
  permutation_upper _ _ _ [258,96,33,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5277

theorem m7230_36 : Upper (D 3) (R 3) [258,96,129,144,36] 13 :=
  permutation_upper _ _ _ [258,96,40,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5284

theorem m7230_40 : Upper (D 3) (R 3) [258,96,129,144,40] 13 :=
  permutation_upper _ _ _ [258,96,40,132,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5286

theorem m7230_96 : Upper (D 3) (R 3) [258,96,129,144,96] 13 :=
  permutation_upper _ _ _ [258,96,96,129,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5293

def r7230 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c7230 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7230 : Upper (D 3) (R 3) [258,96,129,144] 13 := by
  apply FastRouting.sound _ _ [258,96,129,144] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r7230 c7230
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7230_5
  · exact m7230_9
  · exact m7230_12
  · exact m7230_33
  · exact m7230_36
  · exact m7230_40
  · exact m7230_96

theorem m7231_5 : Upper (D 3) (R 3) [258,96,129,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5246

theorem m7231_9 : Upper (D 3) (R 3) [258,96,129,160,9] 13 :=
  permutation_upper _ _ _ [258,96,9,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5258

theorem m7231_12 : Upper (D 3) (R 3) [258,96,129,160,12] 13 :=
  permutation_upper _ _ _ [258,96,24,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5270

theorem m7231_65 : Upper (D 3) (R 3) [258,96,129,160,65] 13 :=
  permutation_upper _ _ _ [258,96,33,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5278

theorem m7231_68 : Upper (D 3) (R 3) [258,96,129,160,68] 13 :=
  permutation_upper _ _ _ [258,96,40,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5285

theorem m7231_72 : Upper (D 3) (R 3) [258,96,129,160,72] 13 :=
  permutation_upper _ _ _ [258,96,40,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5291

def r7231 : Route 9 := (fun mask => (mask,id))

def c7231 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7231 : Upper (D 3) (R 3) [258,96,129,160] 13 := by
  apply FastRouting.sound _ _ [258,96,129,160] 13 (by decide) (choices 2) [5,9,12,65,68,72] r7231 c7231
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7231_5
  · exact m7231_9
  · exact m7231_12
  · exact m7231_65
  · exact m7231_68
  · exact m7231_72

def b7232 : PairBound 9 := { available := 113, camps := [{ cop := 7, region := 12, targets := 1 }], pairs := [(2,0)], upper := (rows 259 98 140 140 113 113 113 241 369), lower := (rows 259 98 140 140 16 32 64 128 256), losses := [] }

theorem u7232 : Upper (D 3) (R 3) [258,96,136,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7232
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7233 : PairBound 9 := { available := 101, camps := [{ cop := 2, region := 355, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 140 152 117 101 101 229 357), lower := (rows 259 98 140 152 16 32 64 128 256), losses := [] }

theorem u7233 : Upper (D 3) (R 3) [258,96,136,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7233
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7234 : PairBound 9 := { available := 85, camps := [{ cop := 2, region := 371, targets := 128 }], pairs := [(0,7)], upper := (rows 259 98 140 168 85 117 85 213 341), lower := (rows 259 98 140 168 16 32 64 128 256), losses := [] }

theorem u7234 : Upper (D 3) (R 3) [258,96,136,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7234
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7235_5 : Upper (D 3) (R 3) [258,96,144,160,5] 13 :=
  permutation_upper _ _ _ [258,96,9,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5250

theorem m7235_9 : Upper (D 3) (R 3) [258,96,144,160,9] 13 :=
  permutation_upper _ _ _ [258,96,9,160,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5259

theorem m7235_12 : Upper (D 3) (R 3) [258,96,144,160,12] 13 :=
  permutation_upper _ _ _ [258,96,24,132,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5271

theorem m7235_65 : Upper (D 3) (R 3) [258,96,144,160,65] 13 :=
  permutation_upper _ _ _ [258,96,33,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5279

theorem m7235_68 : Upper (D 3) (R 3) [258,96,144,160,68] 13 :=
  permutation_upper _ _ _ [258,96,40,132,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5287

theorem m7235_72 : Upper (D 3) (R 3) [258,96,144,160,72] 13 :=
  permutation_upper _ _ _ [258,96,40,192,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5292

def r7235 : Route 9 := (fun mask => (mask,id))

def c7235 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u7235 : Upper (D 3) (R 3) [258,96,144,160] 13 := by
  apply FastRouting.sound _ _ [258,96,144,160] 13 (by decide) (choices 2) [5,9,12,65,68,72] r7235 c7235
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7235_5
  · exact m7235_9
  · exact m7235_12
  · exact m7235_65
  · exact m7235_68
  · exact m7235_72

theorem m7236_5 : Upper (D 3) (R 3) [258,96,160,192,5] 13 :=
  permutation_upper _ _ _ [258,96,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5260

theorem m7236_9 : Upper (D 3) (R 3) [258,96,160,192,9] 13 :=
  permutation_upper _ _ _ [258,96,9,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5260

theorem m7236_12 : Upper (D 3) (R 3) [258,96,160,192,12] 13 :=
  permutation_upper _ _ _ [258,96,24,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5272

def r7236 : Route 9 := (fun mask => (mask,id))

def c7236 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u7236 : Upper (D 3) (R 3) [258,96,160,192] 13 := by
  apply FastRouting.sound _ _ [258,96,160,192] 13 (by decide) (choices 2) [5,9,12] r7236 c7236
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m7236_5
  · exact m7236_9
  · exact m7236_12

def b7237 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 73 248 248 248 248 504), lower := (rows 289 7 7 73 16 32 64 128 256), losses := [] }

theorem u7237 : Upper (D 3) (R 3) [288,5,3,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7237
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7238 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 104 217 249 217 217 473), lower := (rows 289 7 7 104 16 32 64 128 256), losses := [] }

theorem u7238 : Upper (D 3) (R 3) [288,5,3,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7238
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7239 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 7 200 249 249 249 249 505), lower := (rows 289 7 7 200 16 32 64 128 256), losses := [] }

theorem u7239 : Upper (D 3) (R 3) [288,5,3,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7239
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7240 : PairBound 9 := { available := 225, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 26 241 225 225 225 481), lower := (rows 289 7 13 26 16 32 64 128 256), losses := [] }

theorem u7240 : Upper (D 3) (R 3) [288,5,9,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7240
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7241 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 13 42 209 241 209 209 465), lower := (rows 289 7 13 42 16 32 64 128 256), losses := [] }

theorem u7241 : Upper (D 3) (R 3) [288,5,9,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7242 : PairBound 9 := { available := 242, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 73 242 242 242 242 498), lower := (rows 289 7 13 73 16 32 64 128 256), losses := [] }

theorem u7242 : Upper (D 3) (R 3) [288,5,9,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7242
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7243 : PairBound 9 := { available := 241, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 74 241 241 241 241 497), lower := (rows 289 7 13 74 16 32 64 128 256), losses := [] }

theorem u7243 : Upper (D 3) (R 3) [288,5,9,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7243
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7244 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 104 211 243 211 211 467), lower := (rows 289 7 13 104 16 32 64 128 256), losses := [] }

theorem u7244 : Upper (D 3) (R 3) [288,5,9,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7245 : PairBound 9 := { available := 243, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 13 200 243 243 243 243 499), lower := (rows 289 7 13 200 16 32 64 128 256), losses := [] }

theorem u7245 : Upper (D 3) (R 3) [288,5,9,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7246 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 25 241 225 225 225 481), lower := (rows 289 7 14 25 16 32 64 128 256), losses := [] }

theorem u7246 : Upper (D 3) (R 3) [288,5,10,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7247 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 14, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 14 41 209 241 209 209 465), lower := (rows 289 7 14 41 16 32 64 128 256), losses := [] }

theorem u7247 : Upper (D 3) (R 3) [288,5,10,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7248 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 56 209 225 193 193 449), lower := (rows 289 7 14 56 16 32 64 128 256), losses := [] }

theorem u7248 : Upper (D 3) (R 3) [288,5,10,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7249 : PairBound 9 := { available := 241, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 14 73 241 241 241 241 497), lower := (rows 289 7 14 73 16 32 64 128 256), losses := [] }

theorem u7249 : Upper (D 3) (R 3) [288,5,10,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7250 : Route 9 := (fun mask => (mask,id))

def c7250 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7250 : Upper (D 3) (R 3) [288,5,10,80] 13 := by
  apply FastRouting.sound _ _ [288,5,10,80] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7250 c7250
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5351
  · exact u5352
  · exact u5353
  · exact u5354
  · exact u5355
  · exact u5356

def b7251 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 14 104 209 241 209 209 465), lower := (rows 289 7 14 104 16 32 64 128 256), losses := [] }

theorem u7251 : Upper (D 3) (R 3) [288,5,10,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7252 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7252 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7252 : Upper (D 3) (R 3) [288,5,10,192] 13 := by
  apply FastRouting.sound _ _ [288,5,10,192] 13 (by decide) (choices 2) [33,65,96,192] r7252 c7252
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u5360
  · exact u5361
  · exact u5362
  · exact u5363

def b7253 : PairBound 9 := { available := 201, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 42 217 233 201 201 457), lower := (rows 289 7 21 42 16 32 64 128 256), losses := [] }

theorem u7253 : Upper (D 3) (R 3) [288,5,17,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7254 : PairBound 9 := { available := 234, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 73 250 234 234 234 490), lower := (rows 289 7 21 73 16 32 64 128 256), losses := [] }

theorem u7254 : Upper (D 3) (R 3) [288,5,17,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7255 : PairBound 9 := { available := 233, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 74 249 233 233 233 489), lower := (rows 289 7 21 74 16 32 64 128 256), losses := [] }

theorem u7255 : Upper (D 3) (R 3) [288,5,17,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7256 : PairBound 9 := { available := 203, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 104 219 235 203 203 459), lower := (rows 289 7 21 104 16 32 64 128 256), losses := [] }

theorem u7256 : Upper (D 3) (R 3) [288,5,17,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7256
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7257 : PairBound 9 := { available := 235, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 21 200 251 235 235 235 491), lower := (rows 289 7 21 200 16 32 64 128 256), losses := [] }

theorem u7257 : Upper (D 3) (R 3) [288,5,17,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7257
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7258_9 : Upper (D 3) (R 3) [288,5,18,65,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5339

theorem m7258_33 : Upper (D 3) (R 3) [288,5,18,65,33] 13 :=
  permutation_upper _ _ _ [288,5,10,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5342

theorem m7258_40 : Upper (D 3) (R 3) [288,5,18,65,40] 13 :=
  permutation_upper _ _ _ [288,5,10,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5344

theorem m7258_65 : Upper (D 3) (R 3) [288,5,18,65,65] 13 :=
  permutation_upper _ _ _ [288,5,10,65,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5346

theorem m7258_72 : Upper (D 3) (R 3) [288,5,18,65,72] 13 :=
  permutation_upper _ _ _ [288,5,10,80,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5352

theorem m7258_96 : Upper (D 3) (R 3) [288,5,18,65,96] 13 :=
  permutation_upper _ _ _ [288,5,10,96,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5357

theorem m7258_129 : Upper (D 3) (R 3) [288,5,18,65,129] 13 :=
  permutation_upper _ _ _ [288,5,10,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5348

theorem m7258_136 : Upper (D 3) (R 3) [288,5,18,65,136] 13 :=
  permutation_upper _ _ _ [288,5,10,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5354

theorem m7258_160 : Upper (D 3) (R 3) [288,5,18,65,160] 13 :=
  permutation_upper _ _ _ [288,5,10,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5358

theorem m7258_192 : Upper (D 3) (R 3) [288,5,18,65,192] 13 :=
  permutation_upper _ _ _ [288,5,10,192,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5361

def r7258 : Route 9 := (fun mask => (mask,id))

def c7258 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7258 : Upper (D 3) (R 3) [288,5,18,65] 13 := by
  apply FastRouting.sound _ _ [288,5,18,65] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7258 c7258
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7258_9
  · exact m7258_33
  · exact m7258_40
  · exact m7258_65
  · exact m7258_72
  · exact m7258_96
  · exact m7258_129
  · exact m7258_136
  · exact m7258_160
  · exact m7258_192

theorem m7259_9 : Upper (D 3) (R 3) [288,5,18,96,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5340

theorem m7259_65 : Upper (D 3) (R 3) [288,5,18,96,65] 13 :=
  permutation_upper _ _ _ [288,5,10,65,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5347

theorem m7259_72 : Upper (D 3) (R 3) [288,5,18,96,72] 13 :=
  permutation_upper _ _ _ [288,5,10,80,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5353

theorem m7259_129 : Upper (D 3) (R 3) [288,5,18,96,129] 13 :=
  permutation_upper _ _ _ [288,5,10,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5349

theorem m7259_136 : Upper (D 3) (R 3) [288,5,18,96,136] 13 :=
  permutation_upper _ _ _ [288,5,10,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5355

theorem m7259_192 : Upper (D 3) (R 3) [288,5,18,96,192] 13 :=
  permutation_upper _ _ _ [288,5,10,192,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5362

def r7259 : Route 9 := (fun mask => (mask,id))

def c7259 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7259 : Upper (D 3) (R 3) [288,5,18,96] 13 := by
  apply FastRouting.sound _ _ [288,5,18,96] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7259 c7259
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7259_9
  · exact m7259_65
  · exact m7259_72
  · exact m7259_129
  · exact m7259_136
  · exact m7259_192

#print axioms u7259
end Delivery.IrregularNine14.P03
