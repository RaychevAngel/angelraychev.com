import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0250
import IrregularNine14P08C0251
import IrregularNine14P08C0252
import IrregularNine14P08C0253
import IrregularNine14P08C0254
import IrregularNine14P08C0255
import IrregularNine14P08C0256
import IrregularNine14P08C0257
import IrregularNine14P08C0258
import IrregularNine14P08C0259
import IrregularNine14P08C0260

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b22080 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 262 200 57 57 121 185 313), lower := (rows 193 7 262 200 16 32 64 128 256), losses := [] }

theorem u22080 : Upper (D 8) (R 8) [192,5,258,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22080 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22081 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 25 242 226 226 226 482), lower := (rows 193 7 268 25 16 32 64 128 256), losses := [] }

theorem u22081 : Upper (D 8) (R 8) [192,5,264,17] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22081 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22082 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22082 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22082 : Upper (D 8) (R 8) [192,5,264,18] 13 := by
  apply FastRouting.sound _ _ [192,5,264,18] 13 (by decide) (choices 2) [33,65,96,192] r22082 c22082
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15458
  · exact u15459
  · exact u15460
  · exact u15461

def b22083 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 7 268 41 242 242 242 242 498), lower := (rows 193 7 268 41 16 32 64 128 256), losses := [] }

theorem u22083 : Upper (D 8) (R 8) [192,5,264,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22083 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22084 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22084 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22084 : Upper (D 8) (R 8) [192,5,264,34] 13 := by
  apply FastRouting.sound _ _ [192,5,264,34] 13 (by decide) (choices 2) [33,65,96,192] r22084 c22084
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15465
  · exact u15466
  · exact u15467
  · exact u15468

theorem m22085_3 : Upper (D 8) (R 8) [192,5,264,48,3] 13 :=
  permutation_upper _ _ _ [192,5,9,272,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15073

def r22085 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22085 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22085 : Upper (D 8) (R 8) [192,5,264,48] 13 := by
  apply FastRouting.sound _ _ [192,5,264,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22085 c22085
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22085_3
  · exact u15469
  · exact u15470
  · exact u15471
  · exact u15472
  · exact u15473
  · exact u15474

def b22086 : PairBound 9 := { available := 178, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 268 73 178 178 242 178 434), lower := (rows 193 7 268 73 16 32 64 128 256), losses := [] }

theorem u22086 : Upper (D 8) (R 8) [192,5,264,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22086 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22087 : PairBound 9 := { available := 177, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 74 177 177 241 177 433), lower := (rows 193 7 268 74 16 32 64 128 256), losses := [] }

theorem u22087 : Upper (D 8) (R 8) [192,5,264,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22087 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22088 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 88 179 163 227 163 419), lower := (rows 193 7 268 88 16 32 64 128 256), losses := [] }

theorem u22088 : Upper (D 8) (R 8) [192,5,264,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22088 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22089 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 176, targets := 64 }], pairs := [(4,6)], upper := (rows 193 7 268 104 179 179 243 179 435), lower := (rows 193 7 268 104 16 32 64 128 256), losses := [] }

theorem u22089 : Upper (D 8) (R 8) [192,5,264,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22089 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22090 : PairBound 9 := { available := 51, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 268 200 51 51 115 179 307), lower := (rows 193 7 268 200 16 32 64 128 256), losses := [] }

theorem u22090 : Upper (D 8) (R 8) [192,5,264,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22090 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22091_10 : Upper (D 8) (R 8) [192,5,272,33,10] 13 :=
  permutation_upper _ _ _ [192,5,264,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15458

theorem m22091_34 : Upper (D 8) (R 8) [192,5,272,33,34] 13 :=
  permutation_upper _ _ _ [192,5,264,34,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15465

theorem m22091_40 : Upper (D 8) (R 8) [192,5,272,33,40] 13 :=
  permutation_upper _ _ _ [192,5,264,48,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15469

theorem m22091_66 : Upper (D 8) (R 8) [192,5,272,33,66] 13 :=
  permutation_upper _ _ _ [192,5,264,66,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15478

theorem m22091_72 : Upper (D 8) (R 8) [192,5,272,33,72] 13 :=
  permutation_upper _ _ _ [192,5,264,80,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15480

theorem m22091_96 : Upper (D 8) (R 8) [192,5,272,33,96] 13 :=
  permutation_upper _ _ _ [192,5,264,96,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15484

theorem m22091_192 : Upper (D 8) (R 8) [192,5,272,33,192] 13 :=
  permutation_upper _ _ _ [192,5,264,192,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15488

def r22091 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22091 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22091 : Upper (D 8) (R 8) [192,5,272,33] 13 := by
  apply FastRouting.sound _ _ [192,5,272,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r22091 c22091
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22091_10
  · exact m22091_34
  · exact m22091_40
  · exact m22091_66
  · exact m22091_72
  · exact m22091_96
  · exact m22091_192

theorem m22092_9 : Upper (D 8) (R 8) [192,5,272,34,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15215

theorem m22092_33 : Upper (D 8) (R 8) [192,5,272,34,33] 13 :=
  permutation_upper _ _ _ [192,5,264,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15462

theorem m22092_40 : Upper (D 8) (R 8) [192,5,272,34,40] 13 :=
  permutation_upper _ _ _ [192,5,264,48,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15470

theorem m22092_65 : Upper (D 8) (R 8) [192,5,272,34,65] 13 :=
  permutation_upper _ _ _ [192,5,264,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15475

theorem m22092_72 : Upper (D 8) (R 8) [192,5,272,34,72] 13 :=
  permutation_upper _ _ _ [192,5,264,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15481

theorem m22092_96 : Upper (D 8) (R 8) [192,5,272,34,96] 13 :=
  permutation_upper _ _ _ [192,5,264,96,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15485

theorem m22092_192 : Upper (D 8) (R 8) [192,5,272,34,192] 13 :=
  permutation_upper _ _ _ [192,5,264,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15489

def r22092 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22092 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22092 : Upper (D 8) (R 8) [192,5,272,34] 13 := by
  apply FastRouting.sound _ _ [192,5,272,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22092 c22092
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22092_9
  · exact m22092_33
  · exact m22092_40
  · exact m22092_65
  · exact m22092_72
  · exact m22092_96
  · exact m22092_192

theorem m22093_9 : Upper (D 8) (R 8) [192,5,272,66,9] 13 :=
  permutation_upper _ _ _ [192,5,72,17,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15333

theorem m22093_33 : Upper (D 8) (R 8) [192,5,272,66,33] 13 :=
  permutation_upper _ _ _ [192,5,264,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15463

theorem m22093_40 : Upper (D 8) (R 8) [192,5,272,66,40] 13 :=
  permutation_upper _ _ _ [192,5,264,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15472

theorem m22093_129 : Upper (D 8) (R 8) [192,5,272,66,129] 13 :=
  permutation_upper _ _ _ [192,5,264,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15476

theorem m22093_136 : Upper (D 8) (R 8) [192,5,272,66,136] 13 :=
  permutation_upper _ _ _ [192,5,264,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15482

theorem m22093_160 : Upper (D 8) (R 8) [192,5,272,66,160] 13 :=
  permutation_upper _ _ _ [192,5,264,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15486

def r22093 : Route 9 := (fun mask => (mask,id))

def c22093 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22093 : Upper (D 8) (R 8) [192,5,272,66] 13 := by
  apply FastRouting.sound _ _ [192,5,272,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22093 c22093
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22093_9
  · exact m22093_33
  · exact m22093_40
  · exact m22093_129
  · exact m22093_136
  · exact m22093_160

theorem m22094_3 : Upper (D 8) (R 8) [192,5,272,96,3] 13 :=
  permutation_upper _ _ _ [192,5,9,258,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15072

theorem m22094_9 : Upper (D 8) (R 8) [192,5,272,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,17,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15383

theorem m22094_10 : Upper (D 8) (R 8) [192,5,272,96,10] 13 :=
  permutation_upper _ _ _ [192,5,264,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15460

theorem m22094_33 : Upper (D 8) (R 8) [192,5,272,96,33] 13 :=
  permutation_upper _ _ _ [192,5,264,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15464

theorem m22094_34 : Upper (D 8) (R 8) [192,5,272,96,34] 13 :=
  permutation_upper _ _ _ [192,5,264,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15467

theorem m22094_40 : Upper (D 8) (R 8) [192,5,272,96,40] 13 :=
  permutation_upper _ _ _ [192,5,264,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15473

theorem m22094_129 : Upper (D 8) (R 8) [192,5,272,96,129] 13 :=
  permutation_upper _ _ _ [192,5,264,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15477

theorem m22094_130 : Upper (D 8) (R 8) [192,5,272,96,130] 13 :=
  permutation_upper _ _ _ [192,5,264,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15479

theorem m22094_136 : Upper (D 8) (R 8) [192,5,272,96,136] 13 :=
  permutation_upper _ _ _ [192,5,264,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15483

theorem m22094_160 : Upper (D 8) (R 8) [192,5,272,96,160] 13 :=
  permutation_upper _ _ _ [192,5,264,96,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15487

def r22094 : Route 9 := (fun mask => (mask,id))

def c22094 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22094 : Upper (D 8) (R 8) [192,5,272,96] 13 := by
  apply FastRouting.sound _ _ [192,5,272,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22094 c22094
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22094_3
  · exact m22094_9
  · exact m22094_10
  · exact m22094_33
  · exact m22094_34
  · exact m22094_40
  · exact m22094_129
  · exact m22094_130
  · exact m22094_136
  · exact m22094_160

theorem m22095_10 : Upper (D 8) (R 8) [192,5,288,17,10] 13 :=
  permutation_upper _ _ _ [192,5,10,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15083

theorem m22095_34 : Upper (D 8) (R 8) [192,5,288,17,34] 13 :=
  permutation_upper _ _ _ [192,5,40,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15216

theorem m22095_40 : Upper (D 8) (R 8) [192,5,288,17,40] 13 :=
  permutation_upper _ _ _ [192,5,34,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15177

theorem m22095_66 : Upper (D 8) (R 8) [192,5,288,17,66] 13 :=
  permutation_upper _ _ _ [192,5,72,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15334

theorem m22095_72 : Upper (D 8) (R 8) [192,5,288,17,72] 13 :=
  permutation_upper _ _ _ [192,5,66,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15319

theorem m22095_96 : Upper (D 8) (R 8) [192,5,288,17,96] 13 :=
  permutation_upper _ _ _ [192,5,96,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15385

theorem m22095_192 : Upper (D 8) (R 8) [192,5,288,17,192] 13 :=
  permutation_upper _ _ _ [192,5,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15422

def r22095 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22095 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22095 : Upper (D 8) (R 8) [192,5,288,17] 13 := by
  apply FastRouting.sound _ _ [192,5,288,17] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r22095 c22095
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22095_10
  · exact m22095_34
  · exact m22095_40
  · exact m22095_66
  · exact m22095_72
  · exact m22095_96
  · exact m22095_192

theorem m22096_9 : Upper (D 8) (R 8) [192,5,288,18,9] 13 :=
  permutation_upper _ _ _ [192,5,10,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15083

def r22096 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22096 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22096 : Upper (D 8) (R 8) [192,5,288,18] 13 := by
  apply FastRouting.sound _ _ [192,5,288,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22096 c22096
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22096_9
  · exact u15490
  · exact u15491
  · exact u15492
  · exact u15493
  · exact u15494
  · exact u15495

theorem m22097_10 : Upper (D 8) (R 8) [192,5,288,33,10] 13 :=
  permutation_upper _ _ _ [192,5,288,18,33] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15490

def r22097 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22097 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22097 : Upper (D 8) (R 8) [192,5,288,33] 13 := by
  apply FastRouting.sound _ _ [192,5,288,33] 13 (by decide) (choices 2) [10,34,40,66,72,96,192] r22097 c22097
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22097_10
  · exact u15496
  · exact u15497
  · exact u15498
  · exact u15499
  · exact u15500
  · exact u15501

theorem m22098_9 : Upper (D 8) (R 8) [192,5,288,34,9] 13 :=
  permutation_upper _ _ _ [192,5,40,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15216

theorem m22098_33 : Upper (D 8) (R 8) [192,5,288,34,33] 13 :=
  permutation_upper _ _ _ [192,5,288,33,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15496

def r22098 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22098 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22098 : Upper (D 8) (R 8) [192,5,288,34] 13 := by
  apply FastRouting.sound _ _ [192,5,288,34] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r22098 c22098
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22098_9
  · exact m22098_33
  · exact u15502
  · exact u15503
  · exact u15504
  · exact u15505
  · exact u15506

theorem m22099_3 : Upper (D 8) (R 8) [192,5,288,48,3] 13 :=
  permutation_upper _ _ _ [192,5,9,288,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15076

theorem m22099_9 : Upper (D 8) (R 8) [192,5,288,48,9] 13 :=
  permutation_upper _ _ _ [192,5,34,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15177

theorem m22099_10 : Upper (D 8) (R 8) [192,5,288,48,10] 13 :=
  permutation_upper _ _ _ [192,5,288,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15491

theorem m22099_33 : Upper (D 8) (R 8) [192,5,288,48,33] 13 :=
  permutation_upper _ _ _ [192,5,288,33,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15497

theorem m22099_34 : Upper (D 8) (R 8) [192,5,288,48,34] 13 :=
  permutation_upper _ _ _ [192,5,288,34,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15502

def r22099 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22099 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22099 : Upper (D 8) (R 8) [192,5,288,48] 13 := by
  apply FastRouting.sound _ _ [192,5,288,48] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r22099 c22099
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22099_3
  · exact m22099_9
  · exact m22099_10
  · exact m22099_33
  · exact m22099_34
  · exact u15507
  · exact u15508
  · exact u15509
  · exact u15510
  · exact u15511
  · exact u15512

def b22100 : PairBound 9 := { available := 186, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 7 292 73 186 186 250 186 442), lower := (rows 193 7 292 73 16 32 64 128 256), losses := [] }

theorem u22100 : Upper (D 8) (R 8) [192,5,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22100 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22101_9 : Upper (D 8) (R 8) [192,5,288,66,9] 13 :=
  permutation_upper _ _ _ [192,5,72,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15334

theorem m22101_33 : Upper (D 8) (R 8) [192,5,288,66,33] 13 :=
  permutation_upper _ _ _ [192,5,288,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15498

theorem m22101_40 : Upper (D 8) (R 8) [192,5,288,66,40] 13 :=
  permutation_upper _ _ _ [192,5,288,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15509

theorem m22101_129 : Upper (D 8) (R 8) [192,5,288,66,129] 13 :=
  permutation_upper _ _ _ [192,5,288,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15513

def r22101 : Route 9 := (fun mask => (mask,id))

def c22101 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22101 : Upper (D 8) (R 8) [192,5,288,66] 13 := by
  apply FastRouting.sound _ _ [192,5,288,66] 13 (by decide) (choices 2) [9,33,40,129,136,160] r22101 c22101
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22101_9
  · exact m22101_33
  · exact m22101_40
  · exact m22101_129
  · exact u15516
  · exact u15517

theorem m22102_3 : Upper (D 8) (R 8) [192,5,288,80,3] 13 :=
  permutation_upper _ _ _ [192,5,9,288,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15077

theorem m22102_9 : Upper (D 8) (R 8) [192,5,288,80,9] 13 :=
  permutation_upper _ _ _ [192,5,66,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15319

theorem m22102_10 : Upper (D 8) (R 8) [192,5,288,80,10] 13 :=
  permutation_upper _ _ _ [192,5,288,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15493

theorem m22102_33 : Upper (D 8) (R 8) [192,5,288,80,33] 13 :=
  permutation_upper _ _ _ [192,5,288,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15499

theorem m22102_34 : Upper (D 8) (R 8) [192,5,288,80,34] 13 :=
  permutation_upper _ _ _ [192,5,288,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15504

theorem m22102_40 : Upper (D 8) (R 8) [192,5,288,80,40] 13 :=
  permutation_upper _ _ _ [192,5,288,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15510

theorem m22102_129 : Upper (D 8) (R 8) [192,5,288,80,129] 13 :=
  permutation_upper _ _ _ [192,5,288,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15514

theorem m22102_130 : Upper (D 8) (R 8) [192,5,288,80,130] 13 :=
  permutation_upper _ _ _ [192,5,288,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15516

def r22102 : Route 9 := (fun mask => (mask,id))

def c22102 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22102 : Upper (D 8) (R 8) [192,5,288,80] 13 := by
  apply FastRouting.sound _ _ [192,5,288,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22102 c22102
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22102_3
  · exact m22102_9
  · exact m22102_10
  · exact m22102_33
  · exact m22102_34
  · exact m22102_40
  · exact m22102_129
  · exact m22102_130
  · exact u15518
  · exact u15519

theorem m22103_3 : Upper (D 8) (R 8) [192,5,288,96,3] 13 :=
  permutation_upper _ _ _ [192,5,9,288,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15078

theorem m22103_9 : Upper (D 8) (R 8) [192,5,288,96,9] 13 :=
  permutation_upper _ _ _ [192,5,96,17,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15385

theorem m22103_10 : Upper (D 8) (R 8) [192,5,288,96,10] 13 :=
  permutation_upper _ _ _ [192,5,288,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15494

theorem m22103_33 : Upper (D 8) (R 8) [192,5,288,96,33] 13 :=
  permutation_upper _ _ _ [192,5,288,33,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15500

theorem m22103_34 : Upper (D 8) (R 8) [192,5,288,96,34] 13 :=
  permutation_upper _ _ _ [192,5,288,34,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15505

theorem m22103_40 : Upper (D 8) (R 8) [192,5,288,96,40] 13 :=
  permutation_upper _ _ _ [192,5,288,48,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15511

theorem m22103_129 : Upper (D 8) (R 8) [192,5,288,96,129] 13 :=
  permutation_upper _ _ _ [192,5,288,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15515

theorem m22103_130 : Upper (D 8) (R 8) [192,5,288,96,130] 13 :=
  permutation_upper _ _ _ [192,5,288,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15517

theorem m22103_136 : Upper (D 8) (R 8) [192,5,288,96,136] 13 :=
  permutation_upper _ _ _ [192,5,288,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15519

def r22103 : Route 9 := (fun mask => (mask,id))

def c22103 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22103 : Upper (D 8) (R 8) [192,5,288,96] 13 := by
  apply FastRouting.sound _ _ [192,5,288,96] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r22103 c22103
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22103_3
  · exact m22103_9
  · exact m22103_10
  · exact m22103_33
  · exact m22103_34
  · exact m22103_40
  · exact m22103_129
  · exact m22103_130
  · exact m22103_136
  · exact u15520

def b22104 : PairBound 9 := { available := 59, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 7 292 200 59 59 123 187 315), lower := (rows 193 7 292 200 16 32 64 128 256), losses := [] }

theorem u22104 : Upper (D 8) (R 8) [192,5,288,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22104 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22105 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 26 185 169 233 169 425), lower := (rows 193 7 324 26 16 32 64 128 256), losses := [] }

theorem u22105 : Upper (D 8) (R 8) [192,5,320,18] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22105 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22106 : PairBound 9 := { available := 186, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 41 186 186 250 186 442), lower := (rows 193 7 324 41 16 32 64 128 256), losses := [] }

theorem u22106 : Upper (D 8) (R 8) [192,5,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22106 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22107 : PairBound 9 := { available := 185, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 42 185 185 249 185 441), lower := (rows 193 7 324 42 16 32 64 128 256), losses := [] }

theorem u22107 : Upper (D 8) (R 8) [192,5,320,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22107 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22108 : PairBound 9 := { available := 57, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 138 57 57 121 185 313), lower := (rows 193 7 324 138 16 32 64 128 256), losses := [] }

theorem u22108 : Upper (D 8) (R 8) [192,5,320,130] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22108 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22109 : PairBound 9 := { available := 59, camps := [{ cop := 1, region := 184, targets := 64 }], pairs := [(3,6)], upper := (rows 193 7 324 168 59 59 123 187 315), lower := (rows 193 7 324 168 16 32 64 128 256), losses := [] }

theorem u22109 : Upper (D 8) (R 8) [192,5,320,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22109 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22110 : PairBound 9 := { available := 482, camps := [{ cop := 1, region := 496, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 21 41 498 482 482 482 482), lower := (rows 193 14 21 41 16 32 64 128 256), losses := [] }

theorem u22110 : Upper (D 8) (R 8) [192,12,17,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22110 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22111_33 : Upper (D 8) (R 8) [192,12,17,34,33] 13 :=
  permutation_upper _ _ _ [192,5,33,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15145

theorem m22111_65 : Upper (D 8) (R 8) [192,12,17,34,65] 13 :=
  permutation_upper _ _ _ [192,5,65,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15297

theorem m22111_96 : Upper (D 8) (R 8) [192,12,17,34,96] 13 :=
  permutation_upper _ _ _ [192,5,96,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15387

theorem m22111_192 : Upper (D 8) (R 8) [192,12,17,34,192] 13 :=
  permutation_upper _ _ _ [192,5,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15423

theorem m22111_257 : Upper (D 8) (R 8) [192,12,17,34,257] 13 :=
  permutation_upper _ _ _ [192,5,257,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15436

theorem m22111_288 : Upper (D 8) (R 8) [192,12,17,34,288] 13 :=
  permutation_upper _ _ _ [192,5,288,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15491

theorem m22111_320 : Upper (D 8) (R 8) [192,12,17,34,320] 13 :=
  permutation_upper _ _ _ [192,5,320,18,40] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15522

def r22111 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22111 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u22111 : Upper (D 8) (R 8) [192,12,17,34] 13 := by
  apply FastRouting.sound _ _ [192,12,17,34] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r22111 c22111
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22111_33
  · exact m22111_65
  · exact m22111_96
  · exact m22111_192
  · exact m22111_257
  · exact m22111_288
  · exact m22111_320

theorem m22112_3 : Upper (D 8) (R 8) [192,12,17,96,3] 13 :=
  permutation_upper _ _ _ [192,5,9,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15048

theorem m22112_33 : Upper (D 8) (R 8) [192,12,17,96,33] 13 :=
  permutation_upper _ _ _ [192,5,33,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15146

theorem m22112_34 : Upper (D 8) (R 8) [192,12,17,96,34] 13 :=
  permutation_upper _ _ _ [192,5,40,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15220

theorem m22112_129 : Upper (D 8) (R 8) [192,12,17,96,129] 13 :=
  permutation_upper _ _ _ [192,5,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15298

theorem m22112_130 : Upper (D 8) (R 8) [192,12,17,96,130] 13 :=
  permutation_upper _ _ _ [192,5,72,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15336

theorem m22112_160 : Upper (D 8) (R 8) [192,12,17,96,160] 13 :=
  permutation_upper _ _ _ [192,5,96,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15388

theorem m22112_257 : Upper (D 8) (R 8) [192,12,17,96,257] 13 :=
  permutation_upper _ _ _ [192,5,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15437

theorem m22112_258 : Upper (D 8) (R 8) [192,12,17,96,258] 13 :=
  permutation_upper _ _ _ [192,5,264,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15460

theorem m22112_288 : Upper (D 8) (R 8) [192,12,17,96,288] 13 :=
  permutation_upper _ _ _ [192,5,288,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15494

theorem m22112_384 : Upper (D 8) (R 8) [192,12,17,96,384] 13 :=
  permutation_upper _ _ _ [192,5,320,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15523

def r22112 : Route 9 := (fun mask => (mask,id))

def c22112 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22112 : Upper (D 8) (R 8) [192,12,17,96] 13 := by
  apply FastRouting.sound _ _ [192,12,17,96] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r22112 c22112
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22112_3
  · exact m22112_33
  · exact m22112_34
  · exact m22112_129
  · exact m22112_130
  · exact m22112_160
  · exact m22112_257
  · exact m22112_258
  · exact m22112_288
  · exact m22112_384

def b22113 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 21 265 242 226 226 226 482), lower := (rows 193 14 21 265 16 32 64 128 256), losses := [] }

theorem u22113 : Upper (D 8) (R 8) [192,12,17,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22113 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22114_33 : Upper (D 8) (R 8) [192,12,17,258,33] 13 :=
  permutation_upper _ _ _ [192,5,33,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15147

theorem m22114_65 : Upper (D 8) (R 8) [192,12,17,258,65] 13 :=
  permutation_upper _ _ _ [192,5,65,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15299

theorem m22114_96 : Upper (D 8) (R 8) [192,12,17,258,96] 13 :=
  permutation_upper _ _ _ [192,5,96,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15390

theorem m22114_192 : Upper (D 8) (R 8) [192,12,17,258,192] 13 :=
  permutation_upper _ _ _ [192,5,192,18,264] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15424

def r22114 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22114 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22114 : Upper (D 8) (R 8) [192,12,17,258] 13 := by
  apply FastRouting.sound _ _ [192,12,17,258] 13 (by decide) (choices 2) [33,65,96,192] r22114 c22114
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22114_33
  · exact m22114_65
  · exact m22114_96
  · exact m22114_192

theorem m22115_3 : Upper (D 8) (R 8) [192,12,17,288,3] 13 :=
  permutation_upper _ _ _ [192,5,9,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15049

theorem m22115_33 : Upper (D 8) (R 8) [192,12,17,288,33] 13 :=
  permutation_upper _ _ _ [192,5,33,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15148

theorem m22115_34 : Upper (D 8) (R 8) [192,12,17,288,34] 13 :=
  permutation_upper _ _ _ [192,5,40,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15223

theorem m22115_65 : Upper (D 8) (R 8) [192,12,17,288,65] 13 :=
  permutation_upper _ _ _ [192,5,65,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15300

theorem m22115_66 : Upper (D 8) (R 8) [192,12,17,288,66] 13 :=
  permutation_upper _ _ _ [192,5,72,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15338

theorem m22115_96 : Upper (D 8) (R 8) [192,12,17,288,96] 13 :=
  permutation_upper _ _ _ [192,5,96,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15391

theorem m22115_192 : Upper (D 8) (R 8) [192,12,17,288,192] 13 :=
  permutation_upper _ _ _ [192,5,192,18,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15425

def r22115 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22115 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22115 : Upper (D 8) (R 8) [192,12,17,288] 13 := by
  apply FastRouting.sound _ _ [192,12,17,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22115 c22115
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22115_3
  · exact m22115_33
  · exact m22115_34
  · exact m22115_65
  · exact m22115_66
  · exact m22115_96
  · exact m22115_192

theorem m22116_3 : Upper (D 8) (R 8) [192,12,17,320,3] 13 :=
  permutation_upper _ _ _ [192,5,9,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15050

theorem m22116_33 : Upper (D 8) (R 8) [192,12,17,320,33] 13 :=
  permutation_upper _ _ _ [192,5,33,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15149

theorem m22116_34 : Upper (D 8) (R 8) [192,12,17,320,34] 13 :=
  permutation_upper _ _ _ [192,5,40,18,320] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15224

theorem m22116_129 : Upper (D 8) (R 8) [192,12,17,320,129] 13 :=
  permutation_upper _ _ _ [192,5,65,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15301

theorem m22116_130 : Upper (D 8) (R 8) [192,12,17,320,130] 13 :=
  permutation_upper _ _ _ [192,5,72,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15339

theorem m22116_160 : Upper (D 8) (R 8) [192,12,17,320,160] 13 :=
  permutation_upper _ _ _ [192,5,96,18,384] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15392

def r22116 : Route 9 := (fun mask => (mask,id))

def c22116 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22116 : Upper (D 8) (R 8) [192,12,17,320] 13 := by
  apply FastRouting.sound _ _ [192,12,17,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22116 c22116
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22116_3
  · exact m22116_33
  · exact m22116_34
  · exact m22116_129
  · exact m22116_130
  · exact m22116_160

def r22117 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22117 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u22117 : Upper (D 8) (R 8) [192,12,18,33] 13 := by
  apply FastRouting.sound _ _ [192,12,18,33] 13 (by decide) (choices 2) [33,65,96,192,257,288,320] r22117 c22117
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u15531
  · exact u15532
  · exact u15533
  · exact u15534
  · exact u15535
  · exact u15536
  · exact u15537

def b22118 : PairBound 9 := { available := 417, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 22 73 433 417 481 417 417), lower := (rows 193 14 22 73 16 32 64 128 256), losses := [] }

theorem u22118 : Upper (D 8) (R 8) [192,12,18,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22118 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22119 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 104 433 417 481 417 417), lower := (rows 193 14 22 104 16 32 64 128 256), losses := [] }

theorem u22119 : Upper (D 8) (R 8) [192,12,18,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22119 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22120 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 22 200 305 289 353 417 289), lower := (rows 193 14 22 200 16 32 64 128 256), losses := [] }

theorem u22120 : Upper (D 8) (R 8) [192,12,18,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22120 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22121_33 : Upper (D 8) (R 8) [192,12,18,257,33] 13 :=
  permutation_upper _ _ _ [192,12,18,33,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15535

theorem m22121_65 : Upper (D 8) (R 8) [192,12,18,257,65] 13 :=
  permutation_upper _ _ _ [192,12,18,65,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15538

theorem m22121_96 : Upper (D 8) (R 8) [192,12,18,257,96] 13 :=
  permutation_upper _ _ _ [192,12,18,96,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15541

theorem m22121_192 : Upper (D 8) (R 8) [192,12,18,257,192] 13 :=
  permutation_upper _ _ _ [192,12,18,192,257] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15544

def r22121 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22121 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22121 : Upper (D 8) (R 8) [192,12,18,257] 13 := by
  apply FastRouting.sound _ _ [192,12,18,257] 13 (by decide) (choices 2) [33,65,96,192] r22121 c22121
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22121_33
  · exact m22121_65
  · exact m22121_96
  · exact m22121_192

theorem m22122_33 : Upper (D 8) (R 8) [192,12,18,288,33] 13 :=
  permutation_upper _ _ _ [192,12,18,33,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15536

theorem m22122_65 : Upper (D 8) (R 8) [192,12,18,288,65] 13 :=
  permutation_upper _ _ _ [192,12,18,65,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15539

theorem m22122_96 : Upper (D 8) (R 8) [192,12,18,288,96] 13 :=
  permutation_upper _ _ _ [192,12,18,96,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15542

theorem m22122_192 : Upper (D 8) (R 8) [192,12,18,288,192] 13 :=
  permutation_upper _ _ _ [192,12,18,192,288] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15545

def r22122 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22122 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22122 : Upper (D 8) (R 8) [192,12,18,288] 13 := by
  apply FastRouting.sound _ _ [192,12,18,288] 13 (by decide) (choices 2) [33,65,96,192] r22122 c22122
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m22122_33
  · exact m22122_65
  · exact m22122_96
  · exact m22122_192

def b22123 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 22 328 177 161 225 161 417), lower := (rows 193 14 22 328 16 32 64 128 256), losses := [] }

theorem u22123 : Upper (D 8) (R 8) [192,12,18,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22123 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22124 : PairBound 9 := { available := 498, camps := [{ cop := 2, region := 10, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 41 498 498 498 498 498), lower := (rows 193 14 37 41 16 32 64 128 256), losses := [] }

theorem u22124 : Upper (D 8) (R 8) [192,12,33,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22124 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22125 : PairBound 9 := { available := 497, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 37 42 497 497 497 497 497), lower := (rows 193 14 37 42 16 32 64 128 256), losses := [] }

theorem u22125 : Upper (D 8) (R 8) [192,12,33,34] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22125 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22126_3 : Upper (D 8) (R 8) [192,12,33,48,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15120

def r22126 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22126 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 6 => 2 | 10 => 3 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | _ => 0)

theorem u22126 : Upper (D 8) (R 8) [192,12,33,48] 13 := by
  apply FastRouting.sound _ _ [192,12,33,48] 13 (by decide) (choices 2) [3,33,34,65,66,96,192,257,258,288,320] r22126 c22126
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22126_3
  · exact u15557
  · exact u15558
  · exact u15559
  · exact u15560
  · exact u15561
  · exact u15562
  · exact u15563
  · exact u15564
  · exact u15565
  · exact u15566

def b22127 : PairBound 9 := { available := 434, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 37 73 434 434 498 434 434), lower := (rows 193 14 37 73 16 32 64 128 256), losses := [] }

theorem u22127 : Upper (D 8) (R 8) [192,12,33,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22127 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22128 : PairBound 9 := { available := 433, camps := [{ cop := 0, region := 308, targets := 64 }], pairs := [(2,6)], upper := (rows 193 14 37 74 433 433 497 433 433), lower := (rows 193 14 37 74 16 32 64 128 256), losses := [] }

theorem u22128 : Upper (D 8) (R 8) [192,12,33,66] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22128 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

theorem m22129_3 : Upper (D 8) (R 8) [192,12,33,80,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15121

def r22129 : Route 9 := (fun mask => (mask,id))

def c22129 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22129 : Upper (D 8) (R 8) [192,12,33,80] 13 := by
  apply FastRouting.sound _ _ [192,12,33,80] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r22129 c22129
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22129_3
  · exact u15577
  · exact u15578
  · exact u15579
  · exact u15580
  · exact u15581
  · exact u15582
  · exact u15583
  · exact u15584
  · exact u15585

theorem m22130_3 : Upper (D 8) (R 8) [192,12,33,96,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15122

def r22130 : Route 9 := (fun mask => (mask,id))

def c22130 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 6 => 2 | 10 => 3 | 66 => 6 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u22130 : Upper (D 8) (R 8) [192,12,33,96] 13 := by
  apply FastRouting.sound _ _ [192,12,33,96] 13 (by decide) (choices 2) [3,33,34,129,130,160,257,258,288,384] r22130 c22130
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22130_3
  · exact u15586
  · exact u15587
  · exact u15588
  · exact u15589
  · exact u15590
  · exact u15591
  · exact u15592
  · exact u15593
  · exact u15594

def b22131 : PairBound 9 := { available := 307, camps := [{ cop := 0, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 193 14 37 200 307 307 371 435 307), lower := (rows 193 14 37 200 16 32 64 128 256), losses := [] }

theorem u22131 : Upper (D 8) (R 8) [192,12,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22131 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22132 : PairBound 9 := { available := 242, camps := [{ cop := 1, region := 240, targets := 1 }], pairs := [(4,0)], upper := (rows 193 14 37 265 242 242 242 242 498), lower := (rows 193 14 37 265 16 32 64 128 256), losses := [] }

theorem u22132 : Upper (D 8) (R 8) [192,12,33,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22132 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r22133 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22133 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22133 : Upper (D 8) (R 8) [192,12,33,258] 13 := by
  apply FastRouting.sound _ _ [192,12,33,258] 13 (by decide) (choices 2) [33,65,96,192] r22133 c22133
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u15602
  · exact u15603
  · exact u15604
  · exact u15605

theorem m22134_3 : Upper (D 8) (R 8) [192,12,33,272,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,258] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15123

def r22134 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22134 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22134 : Upper (D 8) (R 8) [192,12,33,272] 13 := by
  apply FastRouting.sound _ _ [192,12,33,272] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22134 c22134
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22134_3
  · exact u15606
  · exact u15607
  · exact u15608
  · exact u15609
  · exact u15610
  · exact u15611

theorem m22135_3 : Upper (D 8) (R 8) [192,12,33,288,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,288] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15124

def r22135 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c22135 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u22135 : Upper (D 8) (R 8) [192,12,33,288] 13 := by
  apply FastRouting.sound _ _ [192,12,33,288] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r22135 c22135
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22135_3
  · exact u15612
  · exact u15613
  · exact u15614
  · exact u15615
  · exact u15616
  · exact u15617

theorem m22136_3 : Upper (D 8) (R 8) [192,12,33,320,3] 13 :=
  permutation_upper _ _ _ [192,5,24,33,320] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u15125

def r22136 : Route 9 := (fun mask => (mask,id))

def c22136 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 65 => 6 | 257 => 8 | 6 => 2 | 10 => 3 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u22136 : Upper (D 8) (R 8) [192,12,33,320] 13 := by
  apply FastRouting.sound _ _ [192,12,33,320] 13 (by decide) (choices 2) [3,33,34,129,130,160] r22136 c22136
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m22136_3
  · exact u15618
  · exact u15619
  · exact u15620
  · exact u15621
  · exact u15622

def b22137 : PairBound 9 := { available := 481, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 193 14 38 56 497 481 481 481 481), lower := (rows 193 14 38 56 16 32 64 128 256), losses := [] }

theorem u22137 : Upper (D 8) (R 8) [192,12,34,48] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22137 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22138 : PairBound 9 := { available := 433, camps := [{ cop := 3, region := 438, targets := 64 }], pairs := [(1,6)], upper := (rows 193 14 38 73 433 433 497 433 433), lower := (rows 193 14 38 73 16 32 64 128 256), losses := [] }

theorem u22138 : Upper (D 8) (R 8) [192,12,34,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22138 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b22139 : PairBound 9 := { available := 417, camps := [{ cop := 0, region := 304, targets := 64 }], pairs := [(4,6)], upper := (rows 193 14 38 88 433 417 481 417 417), lower := (rows 193 14 38 88 16 32 64 128 256), losses := [] }

theorem u22139 : Upper (D 8) (R 8) [192,12,34,80] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b22139 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u22139
end Delivery.IrregularNine14.P08
