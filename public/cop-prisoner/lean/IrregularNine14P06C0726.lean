import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0671
import IrregularNine14P06C0672
import IrregularNine14P06C0673
import IrregularNine14P06C0674

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b43560 : PairBound 9 := { available := 124, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 262 11 124 124 124 252 380), lower := (rows 97 131 262 11 16 32 64 128 256), losses := [] }

theorem u43560 : Upper (D 6) (R 6) [96,129,258,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43560 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43561 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43561 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43561 : Upper (D 6) (R 6) [96,129,258,5] 13 := by
  apply FastRouting.sound _ _ [96,129,258,5] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r43561 c43561
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40270
  · exact u40271
  · exact u40272
  · exact u40273
  · exact u40274
  · exact u40275
  · exact u40276

def b43562 : PairBound 9 := { available := 125, camps := [{ cop := 2, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 131 262 14 125 125 125 253 381), lower := (rows 97 131 262 14 16 32 64 128 256), losses := [] }

theorem u43562 : Upper (D 6) (R 6) [96,129,258,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43562 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43563_6 : Upper (D 6) (R 6) [96,129,258,17,6] 13 :=
  permutation_upper _ _ _ [96,129,258,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40277

def r43563 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43563 : Nat → Fin 9 := (fun mask => match mask with | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43563 : Upper (D 6) (R 6) [96,129,258,17] 13 := by
  apply FastRouting.sound _ _ [96,129,258,17] 13 (by decide) (choices 2) [6,10,12,34,36,40,96] r43563 c43563
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43563_6
  · exact u40281
  · exact u40282
  · exact u40283
  · exact u40284
  · exact u40285
  · exact u40286

theorem m43564_5 : Upper (D 6) (R 6) [96,129,258,18,5] 13 :=
  permutation_upper _ _ _ [96,129,258,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40271

theorem m43564_9 : Upper (D 6) (R 6) [96,129,258,18,9] 13 :=
  permutation_upper _ _ _ [96,129,258,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40281

def r43564 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43564 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43564 : Upper (D 6) (R 6) [96,129,258,18] 13 := by
  apply FastRouting.sound _ _ [96,129,258,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r43564 c43564
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43564_5
  · exact m43564_9
  · exact u40287
  · exact u40288
  · exact u40289
  · exact u40290
  · exact u40291

theorem m43565_3 : Upper (D 6) (R 6) [96,129,258,20,3] 13 :=
  permutation_upper _ _ _ [96,129,258,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40267

theorem m43565_5 : Upper (D 6) (R 6) [96,129,258,20,5] 13 :=
  permutation_upper _ _ _ [96,129,258,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40272

theorem m43565_6 : Upper (D 6) (R 6) [96,129,258,20,6] 13 :=
  permutation_upper _ _ _ [96,129,258,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40278

theorem m43565_9 : Upper (D 6) (R 6) [96,129,258,20,9] 13 :=
  permutation_upper _ _ _ [96,129,258,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40282

theorem m43565_10 : Upper (D 6) (R 6) [96,129,258,20,10] 13 :=
  permutation_upper _ _ _ [96,129,258,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40287

def r43565 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43565 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43565 : Upper (D 6) (R 6) [96,129,258,20] 13 := by
  apply FastRouting.sound _ _ [96,129,258,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,96] r43565 c43565
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43565_3
  · exact m43565_5
  · exact m43565_6
  · exact m43565_9
  · exact m43565_10
  · exact u40292
  · exact u40293
  · exact u40294
  · exact u40295
  · exact u40296
  · exact u40297

def b43566 : PairBound 9 := { available := 94, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 131 262 41 94 126 94 222 350), lower := (rows 97 131 262 41 16 32 64 128 256), losses := [] }

theorem u43566 : Upper (D 6) (R 6) [96,129,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43566 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43567_5 : Upper (D 6) (R 6) [96,129,258,34,5] 13 :=
  permutation_upper _ _ _ [96,129,258,5,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40273

theorem m43567_9 : Upper (D 6) (R 6) [96,129,258,34,9] 13 :=
  permutation_upper _ _ _ [96,129,258,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40283

theorem m43567_12 : Upper (D 6) (R 6) [96,129,258,34,12] 13 :=
  permutation_upper _ _ _ [96,129,258,20,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40294

theorem m43567_65 : Upper (D 6) (R 6) [96,129,258,34,65] 13 :=
  permutation_upper _ _ _ [96,129,258,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40298

def r43567 : Route 9 := (fun mask => (mask,id))

def c43567 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43567 : Upper (D 6) (R 6) [96,129,258,34] 13 := by
  apply FastRouting.sound _ _ [96,129,258,34] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43567 c43567
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43567_5
  · exact m43567_9
  · exact m43567_12
  · exact m43567_65
  · exact u40301
  · exact u40302

theorem m43568_3 : Upper (D 6) (R 6) [96,129,258,36,3] 13 :=
  permutation_upper _ _ _ [96,129,258,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40268

theorem m43568_5 : Upper (D 6) (R 6) [96,129,258,36,5] 13 :=
  permutation_upper _ _ _ [96,129,258,5,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40274

theorem m43568_6 : Upper (D 6) (R 6) [96,129,258,36,6] 13 :=
  permutation_upper _ _ _ [96,129,258,6,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40279

theorem m43568_9 : Upper (D 6) (R 6) [96,129,258,36,9] 13 :=
  permutation_upper _ _ _ [96,129,258,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40284

theorem m43568_10 : Upper (D 6) (R 6) [96,129,258,36,10] 13 :=
  permutation_upper _ _ _ [96,129,258,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40289

theorem m43568_12 : Upper (D 6) (R 6) [96,129,258,36,12] 13 :=
  permutation_upper _ _ _ [96,129,258,20,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40295

theorem m43568_65 : Upper (D 6) (R 6) [96,129,258,36,65] 13 :=
  permutation_upper _ _ _ [96,129,258,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40299

theorem m43568_66 : Upper (D 6) (R 6) [96,129,258,36,66] 13 :=
  permutation_upper _ _ _ [96,129,258,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40301

def r43568 : Route 9 := (fun mask => (mask,id))

def c43568 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43568 : Upper (D 6) (R 6) [96,129,258,36] 13 := by
  apply FastRouting.sound _ _ [96,129,258,36] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43568 c43568
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43568_3
  · exact m43568_5
  · exact m43568_6
  · exact m43568_9
  · exact m43568_10
  · exact m43568_12
  · exact m43568_65
  · exact m43568_66
  · exact u40303
  · exact u40304

theorem m43569_3 : Upper (D 6) (R 6) [96,129,258,48,3] 13 :=
  permutation_upper _ _ _ [96,129,258,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40269

theorem m43569_5 : Upper (D 6) (R 6) [96,129,258,48,5] 13 :=
  permutation_upper _ _ _ [96,129,258,5,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40275

theorem m43569_6 : Upper (D 6) (R 6) [96,129,258,48,6] 13 :=
  permutation_upper _ _ _ [96,129,258,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40280

theorem m43569_9 : Upper (D 6) (R 6) [96,129,258,48,9] 13 :=
  permutation_upper _ _ _ [96,129,258,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40285

theorem m43569_10 : Upper (D 6) (R 6) [96,129,258,48,10] 13 :=
  permutation_upper _ _ _ [96,129,258,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40290

theorem m43569_12 : Upper (D 6) (R 6) [96,129,258,48,12] 13 :=
  permutation_upper _ _ _ [96,129,258,20,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40296

theorem m43569_65 : Upper (D 6) (R 6) [96,129,258,48,65] 13 :=
  permutation_upper _ _ _ [96,129,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40300

theorem m43569_66 : Upper (D 6) (R 6) [96,129,258,48,66] 13 :=
  permutation_upper _ _ _ [96,129,258,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40302

theorem m43569_68 : Upper (D 6) (R 6) [96,129,258,48,68] 13 :=
  permutation_upper _ _ _ [96,129,258,36,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40304

def r43569 : Route 9 := (fun mask => (mask,id))

def c43569 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43569 : Upper (D 6) (R 6) [96,129,258,48] 13 := by
  apply FastRouting.sound _ _ [96,129,258,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43569 c43569
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43569_3
  · exact m43569_5
  · exact m43569_6
  · exact m43569_9
  · exact m43569_10
  · exact m43569_12
  · exact m43569_65
  · exact m43569_66
  · exact m43569_68
  · exact u40305

def b43570 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 131 262 104 31 63 95 159 287), lower := (rows 97 131 262 104 16 32 64 128 256), losses := [] }

theorem u43570 : Upper (D 6) (R 6) [96,129,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43570 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43571 : PairBound 9 := { available := 118, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 268 11 118 118 118 246 374), lower := (rows 97 131 268 11 16 32 64 128 256), losses := [] }

theorem u43571 : Upper (D 6) (R 6) [96,129,264,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43571 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43572 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43572 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43572 : Upper (D 6) (R 6) [96,129,264,5] 13 := by
  apply FastRouting.sound _ _ [96,129,264,5] 13 (by decide) (choices 2) [6,34,36,96] r43572 c43572
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u40306
  · exact u40307
  · exact u40308
  · exact u40309

def r43573 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43573 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43573 : Upper (D 6) (R 6) [96,129,264,6] 13 := by
  apply FastRouting.sound _ _ [96,129,264,6] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43573 c43573
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40310
  · exact u40311
  · exact u40312
  · exact u40313
  · exact u40314
  · exact u40315
  · exact u40316

def r43574 : Route 9 := (fun mask => match mask with | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43574 : Nat → Fin 9 := (fun mask => match mask with | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43574 : Upper (D 6) (R 6) [96,129,264,17] 13 := by
  apply FastRouting.sound _ _ [96,129,264,17] 13 (by decide) (choices 2) [6,34,36,96] r43574 c43574
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u40317
  · exact u40318
  · exact u40319
  · exact u40320

def r43575 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43575 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43575 : Upper (D 6) (R 6) [96,129,264,18] 13 := by
  apply FastRouting.sound _ _ [96,129,264,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43575 c43575
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40321
  · exact u40322
  · exact u40323
  · exact u40324
  · exact u40325
  · exact u40326
  · exact u40327

def r43576 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43576 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43576 : Upper (D 6) (R 6) [96,129,264,20] 13 := by
  apply FastRouting.sound _ _ [96,129,264,20] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43576 c43576
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40328
  · exact u40329
  · exact u40330
  · exact u40331
  · exact u40332
  · exact u40333
  · exact u40334

def b43577 : PairBound 9 := { available := 86, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 131 268 41 86 118 86 214 342), lower := (rows 97 131 268 41 16 32 64 128 256), losses := [] }

theorem u43577 : Upper (D 6) (R 6) [96,129,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43577 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43578 : Route 9 := (fun mask => (mask,id))

def c43578 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43578 : Upper (D 6) (R 6) [96,129,264,34] 13 := by
  apply FastRouting.sound _ _ [96,129,264,34] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43578 c43578
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40335
  · exact u40336
  · exact u40337
  · exact u40338
  · exact u40339
  · exact u40340

def r43579 : Route 9 := (fun mask => (mask,id))

def c43579 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43579 : Upper (D 6) (R 6) [96,129,264,36] 13 := by
  apply FastRouting.sound _ _ [96,129,264,36] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43579 c43579
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40341
  · exact u40342
  · exact u40343
  · exact u40344
  · exact u40345
  · exact u40346

def r43580 : Route 9 := (fun mask => (mask,id))

def c43580 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43580 : Upper (D 6) (R 6) [96,129,264,48] 13 := by
  apply FastRouting.sound _ _ [96,129,264,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43580 c43580
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40347
  · exact u40348
  · exact u40349
  · exact u40350
  · exact u40351
  · exact u40352

def b43581 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 131 268 104 23 55 87 151 279), lower := (rows 97 131 268 104 16 32 64 128 256), losses := [] }

theorem u43581 : Upper (D 6) (R 6) [96,129,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43581 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b43582 : PairBound 9 := { available := 94, camps := [{ cop := 1, region := 8, targets := 100 }], pairs := [(3,2),(3,5),(3,6)], upper := (rows 97 131 292 11 94 126 94 222 350), lower := (rows 97 131 292 11 16 32 64 128 256), losses := [] }

theorem u43582 : Upper (D 6) (R 6) [96,129,288,3] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43582 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43583 : Route 9 := (fun mask => (mask,id))

def c43583 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43583 : Upper (D 6) (R 6) [96,129,288,5] 13 := by
  apply FastRouting.sound _ _ [96,129,288,5] 13 (by decide) (choices 2) [6,10,12,66,68,72] r43583 c43583
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40359
  · exact u40360
  · exact u40361
  · exact u40362
  · exact u40363
  · exact u40364

theorem m43584_3 : Upper (D 6) (R 6) [96,129,288,6,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40353

theorem m43584_5 : Upper (D 6) (R 6) [96,129,288,6,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40359

def r43584 : Route 9 := (fun mask => (mask,id))

def c43584 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43584 : Upper (D 6) (R 6) [96,129,288,6] 13 := by
  apply FastRouting.sound _ _ [96,129,288,6] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43584 c43584
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43584_3
  · exact m43584_5
  · exact u40365
  · exact u40366
  · exact u40367
  · exact u40368
  · exact u40369
  · exact u40370
  · exact u40371
  · exact u40372

theorem m43585_6 : Upper (D 6) (R 6) [96,129,288,17,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40366

def r43585 : Route 9 := (fun mask => (mask,id))

def c43585 : Nat → Fin 9 := (fun mask => match mask with | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43585 : Upper (D 6) (R 6) [96,129,288,17] 13 := by
  apply FastRouting.sound _ _ [96,129,288,17] 13 (by decide) (choices 2) [6,10,12,66,68,72] r43585 c43585
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43585_6
  · exact u40373
  · exact u40374
  · exact u40375
  · exact u40376
  · exact u40377

theorem m43586_3 : Upper (D 6) (R 6) [96,129,288,18,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40354

theorem m43586_5 : Upper (D 6) (R 6) [96,129,288,18,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40360

theorem m43586_6 : Upper (D 6) (R 6) [96,129,288,18,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40367

theorem m43586_9 : Upper (D 6) (R 6) [96,129,288,18,9] 13 :=
  permutation_upper _ _ _ [96,129,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40373

def r43586 : Route 9 := (fun mask => (mask,id))

def c43586 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43586 : Upper (D 6) (R 6) [96,129,288,18] 13 := by
  apply FastRouting.sound _ _ [96,129,288,18] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43586 c43586
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43586_3
  · exact m43586_5
  · exact m43586_6
  · exact m43586_9
  · exact u40378
  · exact u40379
  · exact u40380
  · exact u40381
  · exact u40382
  · exact u40383

theorem m43587_3 : Upper (D 6) (R 6) [96,129,288,20,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40355

theorem m43587_5 : Upper (D 6) (R 6) [96,129,288,20,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40361

theorem m43587_6 : Upper (D 6) (R 6) [96,129,288,20,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40368

theorem m43587_9 : Upper (D 6) (R 6) [96,129,288,20,9] 13 :=
  permutation_upper _ _ _ [96,129,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40374

theorem m43587_10 : Upper (D 6) (R 6) [96,129,288,20,10] 13 :=
  permutation_upper _ _ _ [96,129,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40379

def r43587 : Route 9 := (fun mask => (mask,id))

def c43587 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43587 : Upper (D 6) (R 6) [96,129,288,20] 13 := by
  apply FastRouting.sound _ _ [96,129,288,20] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43587 c43587
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43587_3
  · exact m43587_5
  · exact m43587_6
  · exact m43587_9
  · exact m43587_10
  · exact u40384
  · exact u40385
  · exact u40386
  · exact u40387
  · exact u40388

def b43588 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 131 292 73 30 62 94 158 286), lower := (rows 97 131 292 73 16 32 64 128 256), losses := [] }

theorem u43588 : Upper (D 6) (R 6) [96,129,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43588 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43589_3 : Upper (D 6) (R 6) [96,129,288,66,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40356

theorem m43589_5 : Upper (D 6) (R 6) [96,129,288,66,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40362

theorem m43589_6 : Upper (D 6) (R 6) [96,129,288,66,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40370

theorem m43589_9 : Upper (D 6) (R 6) [96,129,288,66,9] 13 :=
  permutation_upper _ _ _ [96,129,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40375

theorem m43589_10 : Upper (D 6) (R 6) [96,129,288,66,10] 13 :=
  permutation_upper _ _ _ [96,129,288,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40381

theorem m43589_12 : Upper (D 6) (R 6) [96,129,288,66,12] 13 :=
  permutation_upper _ _ _ [96,129,288,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40386

def r43589 : Route 9 := (fun mask => (mask,id))

def c43589 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43589 : Upper (D 6) (R 6) [96,129,288,66] 13 := by
  apply FastRouting.sound _ _ [96,129,288,66] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43589 c43589
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43589_3
  · exact m43589_5
  · exact m43589_6
  · exact m43589_9
  · exact m43589_10
  · exact m43589_12

theorem m43590_3 : Upper (D 6) (R 6) [96,129,288,68,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40357

theorem m43590_5 : Upper (D 6) (R 6) [96,129,288,68,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40363

theorem m43590_6 : Upper (D 6) (R 6) [96,129,288,68,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40371

theorem m43590_9 : Upper (D 6) (R 6) [96,129,288,68,9] 13 :=
  permutation_upper _ _ _ [96,129,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40376

theorem m43590_10 : Upper (D 6) (R 6) [96,129,288,68,10] 13 :=
  permutation_upper _ _ _ [96,129,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40382

theorem m43590_12 : Upper (D 6) (R 6) [96,129,288,68,12] 13 :=
  permutation_upper _ _ _ [96,129,288,20,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40387

def r43590 : Route 9 := (fun mask => (mask,id))

def c43590 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43590 : Upper (D 6) (R 6) [96,129,288,68] 13 := by
  apply FastRouting.sound _ _ [96,129,288,68] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43590 c43590
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43590_3
  · exact m43590_5
  · exact m43590_6
  · exact m43590_9
  · exact m43590_10
  · exact m43590_12

theorem m43591_3 : Upper (D 6) (R 6) [96,129,288,80,3] 13 :=
  permutation_upper _ _ _ [96,129,288,3,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40358

theorem m43591_5 : Upper (D 6) (R 6) [96,129,288,80,5] 13 :=
  permutation_upper _ _ _ [96,129,288,5,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40364

theorem m43591_6 : Upper (D 6) (R 6) [96,129,288,80,6] 13 :=
  permutation_upper _ _ _ [96,129,288,6,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40372

theorem m43591_9 : Upper (D 6) (R 6) [96,129,288,80,9] 13 :=
  permutation_upper _ _ _ [96,129,288,17,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40377

theorem m43591_10 : Upper (D 6) (R 6) [96,129,288,80,10] 13 :=
  permutation_upper _ _ _ [96,129,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40383

theorem m43591_12 : Upper (D 6) (R 6) [96,129,288,80,12] 13 :=
  permutation_upper _ _ _ [96,129,288,20,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40388

def r43591 : Route 9 := (fun mask => (mask,id))

def c43591 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43591 : Upper (D 6) (R 6) [96,129,288,80] 13 := by
  apply FastRouting.sound _ _ [96,129,288,80] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43591 c43591
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43591_3
  · exact m43591_5
  · exact m43591_6
  · exact m43591_9
  · exact m43591_10
  · exact m43591_12

def r43592 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43592 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43592 : Upper (D 6) (R 6) [96,132,258,3] 13 := by
  apply FastRouting.sound _ _ [96,132,258,3] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r43592 c43592
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40389
  · exact u40390
  · exact u40391
  · exact u40392
  · exact u40393
  · exact u40394
  · exact u40395

def b43593 : PairBound 9 := { available := 121, camps := [{ cop := 3, region := 113, targets := 6 }], pairs := [(0,1),(0,2),(4,1)], upper := (rows 97 134 262 14 121 121 121 249 377), lower := (rows 97 134 262 14 16 32 64 128 256), losses := [] }

theorem u43593 : Upper (D 6) (R 6) [96,132,258,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43593 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43594_3 : Upper (D 6) (R 6) [96,132,258,17,3] 13 :=
  permutation_upper _ _ _ [96,132,258,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40390

theorem m43594_5 : Upper (D 6) (R 6) [96,132,258,17,5] 13 :=
  permutation_upper _ _ _ [96,132,258,3,9] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40390

theorem m43594_6 : Upper (D 6) (R 6) [96,132,258,17,6] 13 :=
  permutation_upper _ _ _ [96,132,258,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40396

theorem m43594_12 : Upper (D 6) (R 6) [96,132,258,17,12] 13 :=
  permutation_upper _ _ _ [96,132,258,17,10] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40399

theorem m43594_36 : Upper (D 6) (R 6) [96,132,258,17,36] 13 :=
  permutation_upper _ _ _ [96,132,258,17,34] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40401

def r43594 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43594 : Nat → Fin 9 := (fun mask => match mask with | 129 => 7 | 257 => 8 | 130 => 7 | 258 => 8 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43594 : Upper (D 6) (R 6) [96,132,258,17] 13 := by
  apply FastRouting.sound _ _ [96,132,258,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,33,34,36,40,96] r43594 c43594
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43594_3
  · exact m43594_5
  · exact m43594_6
  · exact u40398
  · exact u40399
  · exact m43594_12
  · exact u40400
  · exact u40401
  · exact m43594_36
  · exact u40402
  · exact u40403

theorem m43595_5 : Upper (D 6) (R 6) [96,132,258,18,5] 13 :=
  permutation_upper _ _ _ [96,132,258,3,12] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40391

theorem m43595_9 : Upper (D 6) (R 6) [96,132,258,18,9] 13 :=
  permutation_upper _ _ _ [96,132,258,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40399

def r43595 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 72 => (40,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43595 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 132 => 7 | 260 => 8 | 136 => 7 | 264 => 8 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43595 : Upper (D 6) (R 6) [96,132,258,18] 13 := by
  apply FastRouting.sound _ _ [96,132,258,18] 13 (by decide) (choices 2) [5,9,12,33,36,40,96] r43595 c43595
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43595_5
  · exact m43595_9
  · exact u40404
  · exact u40405
  · exact u40406
  · exact u40407
  · exact u40408

def b43596 : PairBound 9 := { available := 95, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 262 41 95 127 95 223 351), lower := (rows 97 134 262 41 16 32 64 128 256), losses := [] }

theorem u43596 : Upper (D 6) (R 6) [96,132,258,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43596 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43597_5 : Upper (D 6) (R 6) [96,132,258,34,5] 13 :=
  permutation_upper _ _ _ [96,132,258,3,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40393

theorem m43597_9 : Upper (D 6) (R 6) [96,132,258,34,9] 13 :=
  permutation_upper _ _ _ [96,132,258,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40401

theorem m43597_12 : Upper (D 6) (R 6) [96,132,258,34,12] 13 :=
  permutation_upper _ _ _ [96,132,258,18,36] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40406

theorem m43597_65 : Upper (D 6) (R 6) [96,132,258,34,65] 13 :=
  permutation_upper _ _ _ [96,132,258,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40409

def r43597 : Route 9 := (fun mask => (mask,id))

def c43597 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43597 : Upper (D 6) (R 6) [96,132,258,34] 13 := by
  apply FastRouting.sound _ _ [96,132,258,34] 13 (by decide) (choices 2) [5,9,12,65,68,72] r43597 c43597
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43597_5
  · exact m43597_9
  · exact m43597_12
  · exact m43597_65
  · exact u40411
  · exact u40412

theorem m43598_3 : Upper (D 6) (R 6) [96,132,258,48,3] 13 :=
  permutation_upper _ _ _ [96,132,258,3,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40394

theorem m43598_5 : Upper (D 6) (R 6) [96,132,258,48,5] 13 :=
  permutation_upper _ _ _ [96,132,258,3,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40394

theorem m43598_6 : Upper (D 6) (R 6) [96,132,258,48,6] 13 :=
  permutation_upper _ _ _ [96,132,258,6,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40397

theorem m43598_9 : Upper (D 6) (R 6) [96,132,258,48,9] 13 :=
  permutation_upper _ _ _ [96,132,258,17,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40402

theorem m43598_10 : Upper (D 6) (R 6) [96,132,258,48,10] 13 :=
  permutation_upper _ _ _ [96,132,258,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40407

theorem m43598_12 : Upper (D 6) (R 6) [96,132,258,48,12] 13 :=
  permutation_upper _ _ _ [96,132,258,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40407

theorem m43598_65 : Upper (D 6) (R 6) [96,132,258,48,65] 13 :=
  permutation_upper _ _ _ [96,132,258,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40410

theorem m43598_66 : Upper (D 6) (R 6) [96,132,258,48,66] 13 :=
  permutation_upper _ _ _ [96,132,258,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40412

theorem m43598_68 : Upper (D 6) (R 6) [96,132,258,48,68] 13 :=
  permutation_upper _ _ _ [96,132,258,34,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40412

def r43598 : Route 9 := (fun mask => (mask,id))

def c43598 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43598 : Upper (D 6) (R 6) [96,132,258,48] 13 := by
  apply FastRouting.sound _ _ [96,132,258,48] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43598 c43598
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43598_3
  · exact m43598_5
  · exact m43598_6
  · exact m43598_9
  · exact m43598_10
  · exact m43598_12
  · exact m43598_65
  · exact m43598_66
  · exact m43598_68
  · exact u40413

def b43599 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 134 262 104 31 63 95 159 287), lower := (rows 97 134 262 104 16 32 64 128 256), losses := [] }

theorem u43599 : Upper (D 6) (R 6) [96,132,258,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43599 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43600 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43600 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43600 : Upper (D 6) (R 6) [96,132,264,3] 13 := by
  apply FastRouting.sound _ _ [96,132,264,3] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43600 c43600
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40414
  · exact u40415
  · exact u40416
  · exact u40417
  · exact u40418
  · exact u40419
  · exact u40420

def r43601 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43601 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43601 : Upper (D 6) (R 6) [96,132,264,5] 13 := by
  apply FastRouting.sound _ _ [96,132,264,5] 13 (by decide) (choices 2) [3,33,34,96] r43601 c43601
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u40421
  · exact u40422
  · exact u40423
  · exact u40424

def b43602 : PairBound 9 := { available := 115, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 268 14 115 115 115 243 371), lower := (rows 97 134 268 14 16 32 64 128 256), losses := [] }

theorem u43602 : Upper (D 6) (R 6) [96,132,264,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43602 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43603 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43603 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43603 : Upper (D 6) (R 6) [96,132,264,17] 13 := by
  apply FastRouting.sound _ _ [96,132,264,17] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43603 c43603
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40425
  · exact u40426
  · exact u40427
  · exact u40428
  · exact u40429
  · exact u40430
  · exact u40431

def r43604 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 68 => (36,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43604 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 129 => 7 | 257 => 8 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 3 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43604 : Upper (D 6) (R 6) [96,132,264,18] 13 := by
  apply FastRouting.sound _ _ [96,132,264,18] 13 (by decide) (choices 2) [3,5,6,33,34,36,96] r43604 c43604
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40432
  · exact u40433
  · exact u40434
  · exact u40435
  · exact u40436
  · exact u40437
  · exact u40438

def r43605 : Route 9 := (fun mask => match mask with | 65 => (33,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | 66 => (34,(fun i => match i.val with | 5 => 6 | 6 => 5 | _ => i)) | _ => (mask,id))

def c43605 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 160 => 7 | 288 => 8 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43605 : Upper (D 6) (R 6) [96,132,264,20] 13 := by
  apply FastRouting.sound _ _ [96,132,264,20] 13 (by decide) (choices 2) [3,33,34,96] r43605 c43605
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u40439
  · exact u40440
  · exact u40441
  · exact u40442

def b43606 : PairBound 9 := { available := 87, camps := [{ cop := 0, region := 8, targets := 70 }], pairs := [(3,1),(3,2),(3,6)], upper := (rows 97 134 268 41 87 119 87 215 343), lower := (rows 97 134 268 41 16 32 64 128 256), losses := [] }

theorem u43606 : Upper (D 6) (R 6) [96,132,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43606 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43607 : Route 9 := (fun mask => (mask,id))

def c43607 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43607 : Upper (D 6) (R 6) [96,132,264,34] 13 := by
  apply FastRouting.sound _ _ [96,132,264,34] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43607 c43607
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40443
  · exact u40444
  · exact u40445
  · exact u40446
  · exact u40447
  · exact u40448

def r43608 : Route 9 := (fun mask => (mask,id))

def c43608 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43608 : Upper (D 6) (R 6) [96,132,264,36] 13 := by
  apply FastRouting.sound _ _ [96,132,264,36] 13 (by decide) (choices 2) [3,65,66] r43608 c43608
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u40449
  · exact u40450
  · exact u40451

def r43609 : Route 9 := (fun mask => (mask,id))

def c43609 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 129 => 7 | 257 => 8 | 10 => 3 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 3 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43609 : Upper (D 6) (R 6) [96,132,264,48] 13 := by
  apply FastRouting.sound _ _ [96,132,264,48] 13 (by decide) (choices 2) [3,5,6,65,66,68] r43609 c43609
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40452
  · exact u40453
  · exact u40454
  · exact u40455
  · exact u40456
  · exact u40457

def b43610 : PairBound 9 := { available := 23, camps := [{ cop := 0, region := 8, targets := 6 },{ cop := 3, region := 1, targets := 2 }], pairs := [(0,1),(3,1),(3,2)], upper := (rows 97 134 268 104 23 55 87 151 279), lower := (rows 97 134 268 104 16 32 64 128 256), losses := [] }

theorem u43610 : Upper (D 6) (R 6) [96,132,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43610 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r43611 : Route 9 := (fun mask => (mask,id))

def c43611 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43611 : Upper (D 6) (R 6) [96,132,288,3] 13 := by
  apply FastRouting.sound _ _ [96,132,288,3] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43611 c43611
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u40458
  · exact u40459
  · exact u40460
  · exact u40461
  · exact u40462
  · exact u40463
  · exact u40464
  · exact u40465
  · exact u40466
  · exact u40467

theorem m43612_3 : Upper (D 6) (R 6) [96,132,288,5,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,5] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40459

def r43612 : Route 9 := (fun mask => (mask,id))

def c43612 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43612 : Upper (D 6) (R 6) [96,132,288,5] 13 := by
  apply FastRouting.sound _ _ [96,132,288,5] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43612 c43612
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43612_3
  · exact u40468
  · exact u40469
  · exact u40470
  · exact u40471
  · exact u40472

def b43613 : PairBound 9 := { available := 91, camps := [{ cop := 1, region := 8, targets := 97 }], pairs := [(3,0),(3,5),(3,6)], upper := (rows 97 134 292 14 91 123 91 219 347), lower := (rows 97 134 292 14 16 32 64 128 256), losses := [] }

theorem u43613 : Upper (D 6) (R 6) [96,132,288,6] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43613 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43614_3 : Upper (D 6) (R 6) [96,132,288,17,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40461

theorem m43614_5 : Upper (D 6) (R 6) [96,132,288,17,5] 13 :=
  permutation_upper _ _ _ [96,132,288,5,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40468

theorem m43614_6 : Upper (D 6) (R 6) [96,132,288,17,6] 13 :=
  permutation_upper _ _ _ [96,132,288,6,9] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40473

def r43614 : Route 9 := (fun mask => (mask,id))

def c43614 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43614 : Upper (D 6) (R 6) [96,132,288,17] 13 := by
  apply FastRouting.sound _ _ [96,132,288,17] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43614 c43614
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43614_3
  · exact m43614_5
  · exact m43614_6
  · exact u40477
  · exact u40478
  · exact u40479
  · exact u40480
  · exact u40481
  · exact u40482
  · exact u40483

theorem m43615_3 : Upper (D 6) (R 6) [96,132,288,18,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40462

theorem m43615_5 : Upper (D 6) (R 6) [96,132,288,18,5] 13 :=
  permutation_upper _ _ _ [96,132,288,5,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40469

theorem m43615_6 : Upper (D 6) (R 6) [96,132,288,18,6] 13 :=
  permutation_upper _ _ _ [96,132,288,6,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40474

theorem m43615_9 : Upper (D 6) (R 6) [96,132,288,18,9] 13 :=
  permutation_upper _ _ _ [96,132,288,17,10] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40478

def r43615 : Route 9 := (fun mask => (mask,id))

def c43615 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 129 => 7 | 257 => 8 | 34 => 5 | 130 => 7 | 258 => 8 | 36 => 5 | 132 => 7 | 260 => 8 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43615 : Upper (D 6) (R 6) [96,132,288,18] 13 := by
  apply FastRouting.sound _ _ [96,132,288,18] 13 (by decide) (choices 2) [3,5,6,9,10,12,65,66,68,72] r43615 c43615
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43615_3
  · exact m43615_5
  · exact m43615_6
  · exact m43615_9
  · exact u40484
  · exact u40485
  · exact u40486
  · exact u40487
  · exact u40488
  · exact u40489

theorem m43616_3 : Upper (D 6) (R 6) [96,132,288,20,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40463

theorem m43616_9 : Upper (D 6) (R 6) [96,132,288,20,9] 13 :=
  permutation_upper _ _ _ [96,132,288,17,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40479

theorem m43616_10 : Upper (D 6) (R 6) [96,132,288,20,10] 13 :=
  permutation_upper _ _ _ [96,132,288,18,12] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40485

def r43616 : Route 9 := (fun mask => (mask,id))

def c43616 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 7 | 320 => 8 | 384 => 7 | _ => 0)

theorem u43616 : Upper (D 6) (R 6) [96,132,288,20] 13 := by
  apply FastRouting.sound _ _ [96,132,288,20] 13 (by decide) (choices 2) [3,9,10,65,66,72] r43616 c43616
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43616_3
  · exact m43616_9
  · exact m43616_10
  · exact u40490
  · exact u40491
  · exact u40492

def b43617 : PairBound 9 := { available := 31, camps := [{ cop := 0, region := 8, targets := 38 }], pairs := [(3,1),(3,2),(3,5)], upper := (rows 97 134 292 73 31 63 95 159 287), lower := (rows 97 134 292 73 16 32 64 128 256), losses := [] }

theorem u43617 : Upper (D 6) (R 6) [96,132,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 6) 14 b43617 []
    (constants 6).1 (constants 6).2 (by decide +kernel)

theorem m43618_3 : Upper (D 6) (R 6) [96,132,288,66,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40465

theorem m43618_5 : Upper (D 6) (R 6) [96,132,288,66,5] 13 :=
  permutation_upper _ _ _ [96,132,288,5,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40471

theorem m43618_6 : Upper (D 6) (R 6) [96,132,288,66,6] 13 :=
  permutation_upper _ _ _ [96,132,288,6,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40475

theorem m43618_9 : Upper (D 6) (R 6) [96,132,288,66,9] 13 :=
  permutation_upper _ _ _ [96,132,288,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40481

theorem m43618_10 : Upper (D 6) (R 6) [96,132,288,66,10] 13 :=
  permutation_upper _ _ _ [96,132,288,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40487

theorem m43618_12 : Upper (D 6) (R 6) [96,132,288,66,12] 13 :=
  permutation_upper _ _ _ [96,132,288,20,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40491

def r43618 : Route 9 := (fun mask => (mask,id))

def c43618 : Nat → Fin 9 := (fun mask => match mask with | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 36 => 5 | 68 => 6 | 132 => 7 | 260 => 8 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43618 : Upper (D 6) (R 6) [96,132,288,66] 13 := by
  apply FastRouting.sound _ _ [96,132,288,66] 13 (by decide) (choices 2) [3,5,6,9,10,12] r43618 c43618
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m43618_3
  · exact m43618_5
  · exact m43618_6
  · exact m43618_9
  · exact m43618_10
  · exact m43618_12

theorem m43619_3 : Upper (D 6) (R 6) [96,132,288,68,3] 13 :=
  permutation_upper _ _ _ [96,132,288,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40466

theorem m43619_9 : Upper (D 6) (R 6) [96,132,288,68,9] 13 :=
  permutation_upper _ _ _ [96,132,288,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40482

theorem m43619_10 : Upper (D 6) (R 6) [96,132,288,68,10] 13 :=
  permutation_upper _ _ _ [96,132,288,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u40488

def r43619 : Route 9 := (fun mask => (mask,id))

def c43619 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 129 => 7 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 130 => 7 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 136 => 7 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 7 | _ => 0)

theorem u43619 : Upper (D 6) (R 6) [96,132,288,68] 13 := by
  apply FastRouting.sound _ _ [96,132,288,68] 13 (by decide) (choices 2) [3,9,10] r43619 c43619
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m43619_3
  · exact m43619_9
  · exact m43619_10

#print axioms u43619
end Delivery.IrregularNine14.P06
