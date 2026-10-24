import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0088
import IrregularNine14P03C0089
import IrregularNine14P03C0090
import IrregularNine14P03C0091
import IrregularNine14P03C0092
import IrregularNine14P03C0093
import IrregularNine14P03C0094

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m7320_3 : Upper (D 3) (R 3) [288,5,80,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,66,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5325

theorem m7320_9 : Upper (D 3) (R 3) [288,5,80,192,9] 13 :=
  permutation_upper _ _ _ [288,5,72,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5488

theorem m7320_10 : Upper (D 3) (R 3) [288,5,80,192,10] 13 :=
  permutation_upper _ _ _ [288,5,72,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5494

theorem m7320_33 : Upper (D 3) (R 3) [288,5,80,192,33] 13 :=
  permutation_upper _ _ _ [288,5,72,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5498

theorem m7320_34 : Upper (D 3) (R 3) [288,5,80,192,34] 13 :=
  permutation_upper _ _ _ [288,5,72,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5501

theorem m7320_40 : Upper (D 3) (R 3) [288,5,80,192,40] 13 :=
  permutation_upper _ _ _ [288,5,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5506

theorem m7320_129 : Upper (D 3) (R 3) [288,5,80,192,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5527

theorem m7320_130 : Upper (D 3) (R 3) [288,5,80,192,130] 13 :=
  permutation_upper _ _ _ [288,5,72,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5533

theorem m7320_136 : Upper (D 3) (R 3) [288,5,80,192,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5542

theorem m7320_160 : Upper (D 3) (R 3) [288,5,80,192,160] 13 :=
  permutation_upper _ _ _ [288,5,72,160,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5547

def r7320 : Route 9 := (fun mask => (mask,id))

def c7320 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7320 : Upper (D 3) (R 3) [288,5,80,192] 13 := by
  apply FastRouting.sound _ _ [288,5,80,192] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r7320 c7320
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7320_3
  · exact m7320_9
  · exact m7320_10
  · exact m7320_33
  · exact m7320_34
  · exact m7320_40
  · exact m7320_129
  · exact m7320_130
  · exact m7320_136
  · exact m7320_160

def b7321 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 26 217 233 201 201 457), lower := (rows 289 7 100 26 16 32 64 128 256), losses := [] }

theorem u7321 : Upper (D 3) (R 3) [288,5,96,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7321
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7322 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 73 155 187 219 155 411), lower := (rows 289 7 100 73 16 32 64 128 256), losses := [] }

theorem u7322 : Upper (D 3) (R 3) [288,5,96,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7322
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7323 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 74 153 185 217 153 409), lower := (rows 289 7 100 74 16 32 64 128 256), losses := [] }

theorem u7323 : Upper (D 3) (R 3) [288,5,96,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7323
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7324 : PairBound 9 := { available := 219, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 137 219 251 219 219 475), lower := (rows 289 7 100 137 16 32 64 128 256), losses := [] }

theorem u7324 : Upper (D 3) (R 3) [288,5,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7324
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7325 : PairBound 9 := { available := 217, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 138 217 249 217 217 473), lower := (rows 289 7 100 138 16 32 64 128 256), losses := [] }

theorem u7325 : Upper (D 3) (R 3) [288,5,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7325
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7326 : PairBound 9 := { available := 155, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 100 200 155 187 219 155 411), lower := (rows 289 7 100 200 16 32 64 128 256), losses := [] }

theorem u7326 : Upper (D 3) (R 3) [288,5,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7326
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7327_3 : Upper (D 3) (R 3) [288,5,192,17,3] 13 :=
  permutation_upper _ _ _ [288,5,9,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5306

theorem m7327_9 : Upper (D 3) (R 3) [288,5,192,17,9] 13 :=
  permutation_upper _ _ _ [288,5,3,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5295

theorem m7327_10 : Upper (D 3) (R 3) [288,5,192,17,10] 13 :=
  permutation_upper _ _ _ [288,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5341

theorem m7327_33 : Upper (D 3) (R 3) [288,5,192,17,33] 13 :=
  permutation_upper _ _ _ [288,5,33,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5383

theorem m7327_34 : Upper (D 3) (R 3) [288,5,192,17,34] 13 :=
  permutation_upper _ _ _ [288,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5401

theorem m7327_40 : Upper (D 3) (R 3) [288,5,192,17,40] 13 :=
  permutation_upper _ _ _ [288,5,34,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5395

theorem m7327_65 : Upper (D 3) (R 3) [288,5,192,17,65] 13 :=
  permutation_upper _ _ _ [288,5,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5419

theorem m7327_66 : Upper (D 3) (R 3) [288,5,192,17,66] 13 :=
  permutation_upper _ _ _ [288,5,72,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5488

theorem m7327_72 : Upper (D 3) (R 3) [288,5,192,17,72] 13 :=
  permutation_upper _ _ _ [288,5,66,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5460

theorem m7327_96 : Upper (D 3) (R 3) [288,5,192,17,96] 13 :=
  permutation_upper _ _ _ [288,5,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5552

def r7327 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7327 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7327 : Upper (D 3) (R 3) [288,5,192,17] 13 := by
  apply FastRouting.sound _ _ [288,5,192,17] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,192] r7327 c7327
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7327_3
  · exact m7327_9
  · exact m7327_10
  · exact m7327_33
  · exact m7327_34
  · exact m7327_40
  · exact m7327_65
  · exact m7327_66
  · exact m7327_72
  · exact m7327_96
  · exact u5569

theorem m7328_9 : Upper (D 3) (R 3) [288,5,192,18,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5341

def r7328 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7328 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7328 : Upper (D 3) (R 3) [288,5,192,18] 13 := by
  apply FastRouting.sound _ _ [288,5,192,18] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r7328 c7328
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7328_9
  · exact u5570
  · exact u5571
  · exact u5572
  · exact u5573
  · exact u5574
  · exact u5575

def b7329 : PairBound 9 := { available := 219, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 196 41 219 251 219 219 475), lower := (rows 289 7 196 41 16 32 64 128 256), losses := [] }

theorem u7329 : Upper (D 3) (R 3) [288,5,192,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7329
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7330_9 : Upper (D 3) (R 3) [288,5,192,34,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5401

def r7330 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7330 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7330 : Upper (D 3) (R 3) [288,5,192,34] 13 := by
  apply FastRouting.sound _ _ [288,5,192,34] 13 (by decide) (choices 2) [9,65,72,192] r7330 c7330
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7330_9
  · exact u5578
  · exact u5579
  · exact u5580

theorem m7331_3 : Upper (D 3) (R 3) [288,5,192,48,3] 13 :=
  permutation_upper _ _ _ [288,5,9,192,34] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5335

theorem m7331_9 : Upper (D 3) (R 3) [288,5,192,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5395

theorem m7331_10 : Upper (D 3) (R 3) [288,5,192,48,10] 13 :=
  permutation_upper _ _ _ [288,5,192,18,40] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5571

def r7331 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7331 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7331 : Upper (D 3) (R 3) [288,5,192,48] 13 := by
  apply FastRouting.sound _ _ [288,5,192,48] 13 (by decide) (choices 2) [3,9,10,65,66,72,192] r7331 c7331
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7331_3
  · exact m7331_9
  · exact m7331_10
  · exact u5581
  · exact u5582
  · exact u5583
  · exact u5584

theorem m7332_3 : Upper (D 3) (R 3) [288,5,192,65,3] 13 :=
  permutation_upper _ _ _ [288,5,9,192,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5336

theorem m7332_9 : Upper (D 3) (R 3) [288,5,192,65,9] 13 :=
  permutation_upper _ _ _ [288,5,65,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5419

theorem m7332_10 : Upper (D 3) (R 3) [288,5,192,65,10] 13 :=
  permutation_upper _ _ _ [288,5,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5572

theorem m7332_33 : Upper (D 3) (R 3) [288,5,192,65,33] 13 :=
  permutation_upper _ _ _ [288,5,192,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5576

theorem m7332_34 : Upper (D 3) (R 3) [288,5,192,65,34] 13 :=
  permutation_upper _ _ _ [288,5,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5578

theorem m7332_40 : Upper (D 3) (R 3) [288,5,192,65,40] 13 :=
  permutation_upper _ _ _ [288,5,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5581

def r7332 : Route 9 := (fun mask => (mask,id))

def c7332 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7332 : Upper (D 3) (R 3) [288,5,192,65] 13 := by
  apply FastRouting.sound _ _ [288,5,192,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r7332 c7332
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7332_3
  · exact m7332_9
  · exact m7332_10
  · exact m7332_33
  · exact m7332_34
  · exact m7332_40
  · exact u5585
  · exact u5586
  · exact u5587
  · exact u5588

def b7333 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 196 74 185 185 249 185 441), lower := (rows 289 7 196 74 16 32 64 128 256), losses := [] }

theorem u7333 : Upper (D 3) (R 3) [288,5,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7333
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7334_3 : Upper (D 3) (R 3) [288,5,192,80,3] 13 :=
  permutation_upper _ _ _ [288,5,9,192,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5337

theorem m7334_9 : Upper (D 3) (R 3) [288,5,192,80,9] 13 :=
  permutation_upper _ _ _ [288,5,66,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5460

theorem m7334_10 : Upper (D 3) (R 3) [288,5,192,80,10] 13 :=
  permutation_upper _ _ _ [288,5,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5573

theorem m7334_33 : Upper (D 3) (R 3) [288,5,192,80,33] 13 :=
  permutation_upper _ _ _ [288,5,192,33,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5577

theorem m7334_34 : Upper (D 3) (R 3) [288,5,192,80,34] 13 :=
  permutation_upper _ _ _ [288,5,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5579

theorem m7334_40 : Upper (D 3) (R 3) [288,5,192,80,40] 13 :=
  permutation_upper _ _ _ [288,5,192,48,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5583

theorem m7334_129 : Upper (D 3) (R 3) [288,5,192,80,129] 13 :=
  permutation_upper _ _ _ [288,5,192,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5587

theorem m7334_130 : Upper (D 3) (R 3) [288,5,192,80,130] 13 :=
  permutation_upper _ _ _ [288,5,192,66,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5589

def r7334 : Route 9 := (fun mask => (mask,id))

def c7334 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7334 : Upper (D 3) (R 3) [288,5,192,80] 13 := by
  apply FastRouting.sound _ _ [288,5,192,80] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r7334 c7334
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7334_3
  · exact m7334_9
  · exact m7334_10
  · exact m7334_33
  · exact m7334_34
  · exact m7334_40
  · exact m7334_129
  · exact m7334_130
  · exact u5591
  · exact u5592

theorem m7335_3 : Upper (D 3) (R 3) [288,5,192,96,3] 13 :=
  permutation_upper _ _ _ [288,5,9,192,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5338

theorem m7335_9 : Upper (D 3) (R 3) [288,5,192,96,9] 13 :=
  permutation_upper _ _ _ [288,5,96,17,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5552

theorem m7335_10 : Upper (D 3) (R 3) [288,5,192,96,10] 13 :=
  permutation_upper _ _ _ [288,5,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5574

theorem m7335_129 : Upper (D 3) (R 3) [288,5,192,96,129] 13 :=
  permutation_upper _ _ _ [288,5,192,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5588

theorem m7335_130 : Upper (D 3) (R 3) [288,5,192,96,130] 13 :=
  permutation_upper _ _ _ [288,5,192,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5590

theorem m7335_136 : Upper (D 3) (R 3) [288,5,192,96,136] 13 :=
  permutation_upper _ _ _ [288,5,192,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5592

def r7335 : Route 9 := (fun mask => (mask,id))

def c7335 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7335 : Upper (D 3) (R 3) [288,5,192,96] 13 := by
  apply FastRouting.sound _ _ [288,5,192,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r7335 c7335
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7335_3
  · exact m7335_9
  · exact m7335_10
  · exact m7335_129
  · exact m7335_130
  · exact m7335_136

def b7336 : PairBound 9 := { available := 59, camps := [{ cop := 2, region := 8, targets := 1 }], pairs := [(3,0)], upper := (rows 289 7 196 200 59 59 123 187 315), lower := (rows 289 7 196 200 16 32 64 128 256), losses := [] }

theorem u7336 : Upper (D 3) (R 3) [288,5,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7336
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7337_3 : Upper (D 3) (R 3) [288,12,17,65,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5307

theorem m7337_33 : Upper (D 3) (R 3) [288,12,17,65,33] 13 :=
  permutation_upper _ _ _ [288,5,33,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5384

theorem m7337_34 : Upper (D 3) (R 3) [288,12,17,65,34] 13 :=
  permutation_upper _ _ _ [288,5,40,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5402

theorem m7337_65 : Upper (D 3) (R 3) [288,12,17,65,65] 13 :=
  permutation_upper _ _ _ [288,5,65,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5420

theorem m7337_66 : Upper (D 3) (R 3) [288,12,17,65,66] 13 :=
  permutation_upper _ _ _ [288,5,72,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5490

theorem m7337_96 : Upper (D 3) (R 3) [288,12,17,65,96] 13 :=
  permutation_upper _ _ _ [288,5,96,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5553

theorem m7337_129 : Upper (D 3) (R 3) [288,12,17,65,129] 13 :=
  permutation_upper _ _ _ [288,5,65,18,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5423

theorem m7337_130 : Upper (D 3) (R 3) [288,12,17,65,130] 13 :=
  permutation_upper _ _ _ [288,5,72,18,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5492

theorem m7337_160 : Upper (D 3) (R 3) [288,12,17,65,160] 13 :=
  permutation_upper _ _ _ [288,5,96,18,129] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5555

theorem m7337_192 : Upper (D 3) (R 3) [288,12,17,65,192] 13 :=
  permutation_upper _ _ _ [288,5,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5572

def r7337 : Route 9 := (fun mask => (mask,id))

def c7337 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7337 : Upper (D 3) (R 3) [288,12,17,65] 13 := by
  apply FastRouting.sound _ _ [288,12,17,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7337 c7337
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7337_3
  · exact m7337_33
  · exact m7337_34
  · exact m7337_65
  · exact m7337_66
  · exact m7337_96
  · exact m7337_129
  · exact m7337_130
  · exact m7337_160
  · exact m7337_192

theorem m7338_33 : Upper (D 3) (R 3) [288,12,17,66,33] 13 :=
  permutation_upper _ _ _ [288,5,33,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5385

theorem m7338_65 : Upper (D 3) (R 3) [288,12,17,66,65] 13 :=
  permutation_upper _ _ _ [288,5,65,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5421

theorem m7338_96 : Upper (D 3) (R 3) [288,12,17,66,96] 13 :=
  permutation_upper _ _ _ [288,5,96,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5554

theorem m7338_129 : Upper (D 3) (R 3) [288,12,17,66,129] 13 :=
  permutation_upper _ _ _ [288,5,65,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5424

theorem m7338_160 : Upper (D 3) (R 3) [288,12,17,66,160] 13 :=
  permutation_upper _ _ _ [288,5,96,18,136] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5556

theorem m7338_192 : Upper (D 3) (R 3) [288,12,17,66,192] 13 :=
  permutation_upper _ _ _ [288,5,192,18,72] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5573

def r7338 : Route 9 := (fun mask => (mask,id))

def c7338 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7338 : Upper (D 3) (R 3) [288,12,17,66] 13 := by
  apply FastRouting.sound _ _ [288,12,17,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7338 c7338
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7338_33
  · exact m7338_65
  · exact m7338_96
  · exact m7338_129
  · exact m7338_160
  · exact m7338_192

theorem m7339_3 : Upper (D 3) (R 3) [288,12,17,96,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5308

theorem m7339_65 : Upper (D 3) (R 3) [288,12,17,96,65] 13 :=
  permutation_upper _ _ _ [288,5,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5422

theorem m7339_66 : Upper (D 3) (R 3) [288,12,17,96,66] 13 :=
  permutation_upper _ _ _ [288,5,72,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5491

theorem m7339_129 : Upper (D 3) (R 3) [288,12,17,96,129] 13 :=
  permutation_upper _ _ _ [288,5,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5425

theorem m7339_130 : Upper (D 3) (R 3) [288,12,17,96,130] 13 :=
  permutation_upper _ _ _ [288,5,72,18,160] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5493

theorem m7339_192 : Upper (D 3) (R 3) [288,12,17,96,192] 13 :=
  permutation_upper _ _ _ [288,5,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5574

def r7339 : Route 9 := (fun mask => (mask,id))

def c7339 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7339 : Upper (D 3) (R 3) [288,12,17,96] 13 := by
  apply FastRouting.sound _ _ [288,12,17,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r7339 c7339
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7339_3
  · exact m7339_65
  · exact m7339_66
  · exact m7339_129
  · exact m7339_130
  · exact m7339_192

theorem m7340_3 : Upper (D 3) (R 3) [288,12,17,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5309

theorem m7340_33 : Upper (D 3) (R 3) [288,12,17,192,33] 13 :=
  permutation_upper _ _ _ [288,5,33,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5386

theorem m7340_34 : Upper (D 3) (R 3) [288,12,17,192,34] 13 :=
  permutation_upper _ _ _ [288,5,40,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5403

theorem m7340_65 : Upper (D 3) (R 3) [288,12,17,192,65] 13 :=
  permutation_upper _ _ _ [288,5,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5426

theorem m7340_66 : Upper (D 3) (R 3) [288,12,17,192,66] 13 :=
  permutation_upper _ _ _ [288,5,72,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5494

theorem m7340_96 : Upper (D 3) (R 3) [288,12,17,192,96] 13 :=
  permutation_upper _ _ _ [288,5,96,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5557

theorem m7340_192 : Upper (D 3) (R 3) [288,12,17,192,192] 13 :=
  permutation_upper _ _ _ [288,5,192,18,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 4 | 3 => 1 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5575

def r7340 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7340 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7340 : Upper (D 3) (R 3) [288,12,17,192] 13 := by
  apply FastRouting.sound _ _ [288,12,17,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r7340 c7340
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7340_3
  · exact m7340_33
  · exact m7340_34
  · exact m7340_65
  · exact m7340_66
  · exact m7340_96
  · exact m7340_192

def b7341 : PairBound 9 := { available := 193, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 22 41 209 225 193 193 449), lower := (rows 289 14 22 41 16 32 64 128 256), losses := [] }

theorem u7341 : Upper (D 3) (R 3) [288,12,18,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7341
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7342_33 : Upper (D 3) (R 3) [288,12,18,65,33] 13 :=
  permutation_upper _ _ _ [288,12,18,33,65] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5593

def r7342 : Route 9 := (fun mask => (mask,id))

def c7342 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7342 : Upper (D 3) (R 3) [288,12,18,65] 13 := by
  apply FastRouting.sound _ _ [288,12,18,65] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7342 c7342
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7342_33
  · exact u5595
  · exact u5596
  · exact u5597
  · exact u5598
  · exact u5599

def b7343 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 22 104 209 225 193 193 449), lower := (rows 289 14 22 104 16 32 64 128 256), losses := [] }

theorem u7343 : Upper (D 3) (R 3) [288,12,18,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7343
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7344_33 : Upper (D 3) (R 3) [288,12,18,192,33] 13 :=
  permutation_upper _ _ _ [288,12,18,33,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5594

theorem m7344_65 : Upper (D 3) (R 3) [288,12,18,192,65] 13 :=
  permutation_upper _ _ _ [288,12,18,65,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5599

theorem m7344_96 : Upper (D 3) (R 3) [288,12,18,192,96] 13 :=
  permutation_upper _ _ _ [288,12,18,96,192] (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5600

def r7344 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7344 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7344 : Upper (D 3) (R 3) [288,12,18,192] 13 := by
  apply FastRouting.sound _ _ [288,12,18,192] 13 (by decide) (choices 2) [33,65,96,192] r7344 c7344
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7344_33
  · exact m7344_65
  · exact m7344_96
  · exact u5601

def b7345 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 73 211 243 211 211 467), lower := (rows 289 14 37 73 16 32 64 128 256), losses := [] }

theorem u7345 : Upper (D 3) (R 3) [288,12,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7345
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7346 : PairBound 9 := { available := 209, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 74 209 241 209 209 465), lower := (rows 289 14 37 74 16 32 64 128 256), losses := [] }

theorem u7346 : Upper (D 3) (R 3) [288,12,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7346
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7347 : PairBound 9 := { available := 195, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 88 211 227 195 195 451), lower := (rows 289 14 37 88 16 32 64 128 256), losses := [] }

theorem u7347 : Upper (D 3) (R 3) [288,12,33,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7347
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7348 : PairBound 9 := { available := 211, camps := [{ cop := 2, region := 218, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 37 200 211 243 211 211 467), lower := (rows 289 14 37 200 16 32 64 128 256), losses := [] }

theorem u7348 : Upper (D 3) (R 3) [288,12,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7348
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7349 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 73 209 241 209 209 465), lower := (rows 289 14 38 73 16 32 64 128 256), losses := [] }

theorem u7349 : Upper (D 3) (R 3) [288,12,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7349
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7350 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 88 209 225 193 193 449), lower := (rows 289 14 38 88 16 32 64 128 256), losses := [] }

theorem u7350 : Upper (D 3) (R 3) [288,12,34,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7350
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7351 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 14 38 200 209 241 209 209 465), lower := (rows 289 14 38 200 16 32 64 128 256), losses := [] }

theorem u7351 : Upper (D 3) (R 3) [288,12,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7351
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7352_3 : Upper (D 3) (R 3) [288,12,48,65,3] 13 :=
  permutation_upper _ _ _ [288,5,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5367

def r7352 : Route 9 := (fun mask => (mask,id))

def c7352 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7352 : Upper (D 3) (R 3) [288,12,48,65] 13 := by
  apply FastRouting.sound _ _ [288,12,48,65] 13 (by decide) (choices 2) [3,65,66,129,130,192] r7352 c7352
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7352_3
  · exact u5613
  · exact u5614
  · exact u5615
  · exact u5616
  · exact u5617

def b7353 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 52 74 209 225 193 193 449), lower := (rows 289 14 52 74 16 32 64 128 256), losses := [] }

theorem u7353 : Upper (D 3) (R 3) [288,12,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7353
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7354_3 : Upper (D 3) (R 3) [288,12,48,192,3] 13 :=
  permutation_upper _ _ _ [288,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5368

def r7354 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7354 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7354 : Upper (D 3) (R 3) [288,12,48,192] 13 := by
  apply FastRouting.sound _ _ [288,12,48,192] 13 (by decide) (choices 2) [3,65,66,192] r7354 c7354
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact m7354_3
  · exact u5621
  · exact u5622
  · exact u5623

def b7355 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 10, targets := 32 }], pairs := [(1,5)], upper := (rows 289 14 69 73 179 179 243 179 435), lower := (rows 289 14 69 73 16 32 64 128 256), losses := [] }

theorem u7355 : Upper (D 3) (R 3) [288,12,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7355
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7356 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 69 74 177 177 241 177 433), lower := (rows 289 14 69 74 16 32 64 128 256), losses := [] }

theorem u7356 : Upper (D 3) (R 3) [288,12,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7356
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7357 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 88 179 163 227 163 419), lower := (rows 289 14 69 88 16 32 64 128 256), losses := [] }

theorem u7357 : Upper (D 3) (R 3) [288,12,65,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7357
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7358 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 104 147 179 211 147 403), lower := (rows 289 14 69 104 16 32 64 128 256), losses := [] }

theorem u7358 : Upper (D 3) (R 3) [288,12,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7358
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7359_3 : Upper (D 3) (R 3) [288,12,65,129,3] 13 :=
  permutation_upper _ _ _ [288,5,24,65,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5372

theorem m7359_129 : Upper (D 3) (R 3) [288,12,65,129,129] 13 :=
  permutation_upper _ _ _ [288,12,65,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5638

theorem m7359_130 : Upper (D 3) (R 3) [288,12,65,129,130] 13 :=
  permutation_upper _ _ _ [288,12,65,129,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5639

theorem m7359_160 : Upper (D 3) (R 3) [288,12,65,129,160] 13 :=
  permutation_upper _ _ _ [288,12,65,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5640

def r7359 : Route 9 := (fun mask => (mask,id))

def c7359 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7359 : Upper (D 3) (R 3) [288,12,65,129] 13 := by
  apply FastRouting.sound _ _ [288,12,65,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7359 c7359
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7359_3
  · exact u5636
  · exact u5637
  · exact u5638
  · exact u5639
  · exact u5640
  · exact m7359_129
  · exact m7359_130
  · exact m7359_160
  · exact u5641

def r7360 : Route 9 := (fun mask => (mask,id))

def c7360 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7360 : Upper (D 3) (R 3) [288,12,65,130] 13 := by
  apply FastRouting.sound _ _ [288,12,65,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7360 c7360
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5642
  · exact u5643
  · exact u5644
  · exact u5645
  · exact u5646
  · exact u5647

theorem m7361_3 : Upper (D 3) (R 3) [288,12,65,144,3] 13 :=
  permutation_upper _ _ _ [288,5,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5373

def r7361 : Route 9 := (fun mask => (mask,id))

def c7361 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7361 : Upper (D 3) (R 3) [288,12,65,144] 13 := by
  apply FastRouting.sound _ _ [288,12,65,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7361 c7361
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7361_3
  · exact u5648
  · exact u5649
  · exact u5650
  · exact u5651
  · exact u5652
  · exact u5653
  · exact u5654
  · exact u5655
  · exact u5656

theorem m7362_3 : Upper (D 3) (R 3) [288,12,65,160,3] 13 :=
  permutation_upper _ _ _ [288,5,24,65,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5374

def r7362 : Route 9 := (fun mask => (mask,id))

def c7362 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7362 : Upper (D 3) (R 3) [288,12,65,160] 13 := by
  apply FastRouting.sound _ _ [288,12,65,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r7362 c7362
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7362_3
  · exact u5657
  · exact u5658
  · exact u5659
  · exact u5660
  · exact u5661

def b7363 : PairBound 9 := { available := 179, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 69 200 179 179 243 179 435), lower := (rows 289 14 69 200 16 32 64 128 256), losses := [] }

theorem u7363 : Upper (D 3) (R 3) [288,12,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7363
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7364 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 88 177 161 225 161 417), lower := (rows 289 14 70 88 16 32 64 128 256), losses := [] }

theorem u7364 : Upper (D 3) (R 3) [288,12,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7364
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7365 : PairBound 9 := { available := 145, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 104 145 177 209 145 401), lower := (rows 289 14 70 104 16 32 64 128 256), losses := [] }

theorem u7365 : Upper (D 3) (R 3) [288,12,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7365
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r7366 : Route 9 := (fun mask => (mask,id))

def c7366 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7366 : Upper (D 3) (R 3) [288,12,66,144] 13 := by
  apply FastRouting.sound _ _ [288,12,66,144] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7366 c7366
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5669
  · exact u5670
  · exact u5671
  · exact u5672
  · exact u5673
  · exact u5674

def b7367 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 14 70 168 209 241 209 209 465), lower := (rows 289 14 70 168 16 32 64 128 256), losses := [] }

theorem u7367 : Upper (D 3) (R 3) [288,12,66,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7367
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7368 : PairBound 9 := { available := 177, camps := [{ cop := 3, region := 6, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 70 200 177 177 241 177 433), lower := (rows 289 14 70 200 16 32 64 128 256), losses := [] }

theorem u7368 : Upper (D 3) (R 3) [288,12,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7368
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7369 : PairBound 9 := { available := 131, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 104 147 163 195 131 387), lower := (rows 289 14 84 104 16 32 64 128 256), losses := [] }

theorem u7369 : Upper (D 3) (R 3) [288,12,80,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7369
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7370_3 : Upper (D 3) (R 3) [288,12,80,160,3] 13 :=
  permutation_upper _ _ _ [288,5,24,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5377

def r7370 : Route 9 := (fun mask => (mask,id))

def c7370 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 2 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7370 : Upper (D 3) (R 3) [288,12,80,160] 13 := by
  apply FastRouting.sound _ _ [288,12,80,160] 13 (by decide) (choices 2) [3,65,66,129,130,192] r7370 c7370
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7370_3
  · exact u5682
  · exact u5683
  · exact u5684
  · exact u5685
  · exact u5686

def b7371 : PairBound 9 := { available := 163, camps := [{ cop := 1, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 84 200 179 163 227 163 419), lower := (rows 289 14 84 200 16 32 64 128 256), losses := [] }

theorem u7371 : Upper (D 3) (R 3) [288,12,80,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7371
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7372 : PairBound 9 := { available := 147, camps := [{ cop := 1, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 14 100 200 147 179 211 147 403), lower := (rows 289 14 100 200 16 32 64 128 256), losses := [] }

theorem u7372 : Upper (D 3) (R 3) [288,12,96,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7372
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7373 : PairBound 9 := { available := 51, camps := [{ cop := 2, region := 10, targets := 1 }], pairs := [(1,0)], upper := (rows 289 14 196 200 51 51 115 179 307), lower := (rows 289 14 196 200 16 32 64 128 256), losses := [] }

theorem u7373 : Upper (D 3) (R 3) [288,12,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7373
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7374_5 : Upper (D 3) (R 3) [288,17,34,65,5] 13 :=
  permutation_upper _ _ _ [288,5,9,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5310

theorem m7374_9 : Upper (D 3) (R 3) [288,17,34,65,9] 13 :=
  permutation_upper _ _ _ [288,5,9,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5315

theorem m7374_12 : Upper (D 3) (R 3) [288,17,34,65,12] 13 :=
  permutation_upper _ _ _ [288,5,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5367

theorem m7374_65 : Upper (D 3) (R 3) [288,17,34,65,65] 13 :=
  permutation_upper _ _ _ [288,5,65,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5427

theorem m7374_68 : Upper (D 3) (R 3) [288,17,34,65,68] 13 :=
  permutation_upper _ _ _ [288,5,72,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5499

theorem m7374_72 : Upper (D 3) (R 3) [288,17,34,65,72] 13 :=
  permutation_upper _ _ _ [288,5,72,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5507

theorem m7374_129 : Upper (D 3) (R 3) [288,17,34,65,129] 13 :=
  permutation_upper _ _ _ [288,5,65,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5429

theorem m7374_132 : Upper (D 3) (R 3) [288,17,34,65,132] 13 :=
  permutation_upper _ _ _ [288,5,72,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5500

theorem m7374_136 : Upper (D 3) (R 3) [288,17,34,65,136] 13 :=
  permutation_upper _ _ _ [288,5,72,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5520

theorem m7374_192 : Upper (D 3) (R 3) [288,17,34,65,192] 13 :=
  permutation_upper _ _ _ [288,5,192,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5578

def r7374 : Route 9 := (fun mask => (mask,id))

def c7374 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7374 : Upper (D 3) (R 3) [288,17,34,65] 13 := by
  apply FastRouting.sound _ _ [288,17,34,65] 13 (by decide) (choices 2) [5,9,12,65,68,72,129,132,136,192] r7374 c7374
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7374_5
  · exact m7374_9
  · exact m7374_12
  · exact m7374_65
  · exact m7374_68
  · exact m7374_72
  · exact m7374_129
  · exact m7374_132
  · exact m7374_136
  · exact m7374_192

theorem m7375_9 : Upper (D 3) (R 3) [288,17,34,68,9] 13 :=
  permutation_upper _ _ _ [288,5,9,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5326

theorem m7375_65 : Upper (D 3) (R 3) [288,17,34,68,65] 13 :=
  permutation_upper _ _ _ [288,5,65,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5428

theorem m7375_72 : Upper (D 3) (R 3) [288,17,34,68,72] 13 :=
  permutation_upper _ _ _ [288,5,72,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5513

theorem m7375_129 : Upper (D 3) (R 3) [288,17,34,68,129] 13 :=
  permutation_upper _ _ _ [288,5,65,34,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5430

theorem m7375_136 : Upper (D 3) (R 3) [288,17,34,68,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5535

theorem m7375_192 : Upper (D 3) (R 3) [288,17,34,68,192] 13 :=
  permutation_upper _ _ _ [288,5,192,34,72] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5579

def r7375 : Route 9 := (fun mask => (mask,id))

def c7375 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7375 : Upper (D 3) (R 3) [288,17,34,68] 13 := by
  apply FastRouting.sound _ _ [288,17,34,68] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7375 c7375
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7375_9
  · exact m7375_65
  · exact m7375_72
  · exact m7375_129
  · exact m7375_136
  · exact m7375_192

theorem m7376_5 : Upper (D 3) (R 3) [288,17,34,192,5] 13 :=
  permutation_upper _ _ _ [288,5,9,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5311

theorem m7376_9 : Upper (D 3) (R 3) [288,17,34,192,9] 13 :=
  permutation_upper _ _ _ [288,5,9,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5335

theorem m7376_12 : Upper (D 3) (R 3) [288,17,34,192,12] 13 :=
  permutation_upper _ _ _ [288,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5368

theorem m7376_65 : Upper (D 3) (R 3) [288,17,34,192,65] 13 :=
  permutation_upper _ _ _ [288,5,65,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5431

theorem m7376_68 : Upper (D 3) (R 3) [288,17,34,192,68] 13 :=
  permutation_upper _ _ _ [288,5,72,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5501

theorem m7376_72 : Upper (D 3) (R 3) [288,17,34,192,72] 13 :=
  permutation_upper _ _ _ [288,5,72,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5548

theorem m7376_192 : Upper (D 3) (R 3) [288,17,34,192,192] 13 :=
  permutation_upper _ _ _ [288,5,192,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5580

def r7376 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7376 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 36 => 5 | 260 => 8 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7376 : Upper (D 3) (R 3) [288,17,34,192] 13 := by
  apply FastRouting.sound _ _ [288,17,34,192] 13 (by decide) (choices 2) [5,9,12,65,68,72,192] r7376 c7376
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7376_5
  · exact m7376_9
  · exact m7376_12
  · exact m7376_65
  · exact m7376_68
  · exact m7376_72
  · exact m7376_192

theorem m7377_3 : Upper (D 3) (R 3) [288,17,40,65,3] 13 :=
  permutation_upper _ _ _ [288,5,3,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5296

theorem m7377_5 : Upper (D 3) (R 3) [288,17,40,65,5] 13 :=
  permutation_upper _ _ _ [288,5,9,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5312

theorem m7377_6 : Upper (D 3) (R 3) [288,17,40,65,6] 13 :=
  permutation_upper _ _ _ [288,5,10,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5344

theorem m7377_65 : Upper (D 3) (R 3) [288,17,40,65,65] 13 :=
  permutation_upper _ _ _ [288,5,65,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5432

theorem m7377_66 : Upper (D 3) (R 3) [288,17,40,65,66] 13 :=
  permutation_upper _ _ _ [288,5,66,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5463

theorem m7377_68 : Upper (D 3) (R 3) [288,17,40,65,68] 13 :=
  permutation_upper _ _ _ [288,5,72,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5502

theorem m7377_129 : Upper (D 3) (R 3) [288,17,40,65,129] 13 :=
  permutation_upper _ _ _ [288,5,65,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5434

theorem m7377_130 : Upper (D 3) (R 3) [288,17,40,65,130] 13 :=
  permutation_upper _ _ _ [288,5,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5465

theorem m7377_132 : Upper (D 3) (R 3) [288,17,40,65,132] 13 :=
  permutation_upper _ _ _ [288,5,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5504

theorem m7377_192 : Upper (D 3) (R 3) [288,17,40,65,192] 13 :=
  permutation_upper _ _ _ [288,5,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5581

def r7377 : Route 9 := (fun mask => (mask,id))

def c7377 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7377 : Upper (D 3) (R 3) [288,17,40,65] 13 := by
  apply FastRouting.sound _ _ [288,17,40,65] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r7377 c7377
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7377_3
  · exact m7377_5
  · exact m7377_6
  · exact m7377_65
  · exact m7377_66
  · exact m7377_68
  · exact m7377_129
  · exact m7377_130
  · exact m7377_132
  · exact m7377_192

theorem m7378_5 : Upper (D 3) (R 3) [288,17,40,66,5] 13 :=
  permutation_upper _ _ _ [288,5,9,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5313

theorem m7378_65 : Upper (D 3) (R 3) [288,17,40,66,65] 13 :=
  permutation_upper _ _ _ [288,5,65,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5433

theorem m7378_68 : Upper (D 3) (R 3) [288,17,40,66,68] 13 :=
  permutation_upper _ _ _ [288,5,72,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5503

theorem m7378_129 : Upper (D 3) (R 3) [288,17,40,66,129] 13 :=
  permutation_upper _ _ _ [288,5,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5435

theorem m7378_132 : Upper (D 3) (R 3) [288,17,40,66,132] 13 :=
  permutation_upper _ _ _ [288,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5505

theorem m7378_192 : Upper (D 3) (R 3) [288,17,40,66,192] 13 :=
  permutation_upper _ _ _ [288,5,192,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5582

def r7378 : Route 9 := (fun mask => (mask,id))

def c7378 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 9 => 3 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7378 : Upper (D 3) (R 3) [288,17,40,66] 13 := by
  apply FastRouting.sound _ _ [288,17,40,66] 13 (by decide) (choices 2) [5,65,68,129,132,192] r7378 c7378
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7378_5
  · exact m7378_65
  · exact m7378_68
  · exact m7378_129
  · exact m7378_132
  · exact m7378_192

theorem m7379_3 : Upper (D 3) (R 3) [288,17,40,192,3] 13 :=
  permutation_upper _ _ _ [288,5,3,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5297

theorem m7379_5 : Upper (D 3) (R 3) [288,17,40,192,5] 13 :=
  permutation_upper _ _ _ [288,5,9,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5314

theorem m7379_6 : Upper (D 3) (R 3) [288,17,40,192,6] 13 :=
  permutation_upper _ _ _ [288,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5345

theorem m7379_65 : Upper (D 3) (R 3) [288,17,40,192,65] 13 :=
  permutation_upper _ _ _ [288,5,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5436

theorem m7379_66 : Upper (D 3) (R 3) [288,17,40,192,66] 13 :=
  permutation_upper _ _ _ [288,5,66,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5467

theorem m7379_68 : Upper (D 3) (R 3) [288,17,40,192,68] 13 :=
  permutation_upper _ _ _ [288,5,72,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5506

theorem m7379_192 : Upper (D 3) (R 3) [288,17,40,192,192] 13 :=
  permutation_upper _ _ _ [288,5,192,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 4 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 4 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5584

def r7379 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7379 : Nat → Fin 9 := (fun mask => match mask with | 9 => 3 | 33 => 5 | 257 => 8 | 10 => 3 | 34 => 5 | 258 => 8 | 12 => 3 | 36 => 5 | 260 => 8 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7379 : Upper (D 3) (R 3) [288,17,40,192] 13 := by
  apply FastRouting.sound _ _ [288,17,40,192] 13 (by decide) (choices 2) [3,5,6,65,66,68,192] r7379 c7379
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7379_3
  · exact m7379_5
  · exact m7379_6
  · exact m7379_65
  · exact m7379_66
  · exact m7379_68
  · exact m7379_192

#print axioms u7379
end Delivery.IrregularNine14.P03
