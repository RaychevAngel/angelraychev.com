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

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m7260_9 : Upper (D 3) (R 3) [288,5,18,192,9] 13 :=
  permutation_upper _ _ _ [288,5,10,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5341

theorem m7260_33 : Upper (D 3) (R 3) [288,5,18,192,33] 13 :=
  permutation_upper _ _ _ [288,5,10,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5343

theorem m7260_40 : Upper (D 3) (R 3) [288,5,18,192,40] 13 :=
  permutation_upper _ _ _ [288,5,10,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5345

theorem m7260_65 : Upper (D 3) (R 3) [288,5,18,192,65] 13 :=
  permutation_upper _ _ _ [288,5,10,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5350

theorem m7260_72 : Upper (D 3) (R 3) [288,5,18,192,72] 13 :=
  permutation_upper _ _ _ [288,5,10,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5356

theorem m7260_96 : Upper (D 3) (R 3) [288,5,18,192,96] 13 :=
  permutation_upper _ _ _ [288,5,10,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5359

theorem m7260_192 : Upper (D 3) (R 3) [288,5,18,192,192] 13 :=
  permutation_upper _ _ _ [288,5,10,192,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5363

def r7260 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 136 => (72,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7260 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7260 : Upper (D 3) (R 3) [288,5,18,192] 13 := by
  apply FastRouting.sound _ _ [288,5,18,192] 13 (by decide) (choices 2) [9,33,40,65,72,96,192] r7260 c7260
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7260_9
  · exact m7260_33
  · exact m7260_40
  · exact m7260_65
  · exact m7260_72
  · exact m7260_96
  · exact m7260_192

def b7261 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 28 41 211 227 195 195 451), lower := (rows 289 7 28 41 16 32 64 128 256), losses := [] }

theorem u7261 : Upper (D 3) (R 3) [288,5,24,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7261
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7262 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 28 42 209 225 193 193 449), lower := (rows 289 7 28 42 16 32 64 128 256), losses := [] }

theorem u7262 : Upper (D 3) (R 3) [288,5,24,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7262
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7263_3 : Upper (D 3) (R 3) [288,5,24,65,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5307

theorem m7263_33 : Upper (D 3) (R 3) [288,5,24,65,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5364

theorem m7263_34 : Upper (D 3) (R 3) [288,5,24,65,34] 13 :=
  permutation_upper _ _ _ [288,5,24,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5367

def r7263 : Route 9 := (fun mask => (mask,id))

def c7263 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7263 : Upper (D 3) (R 3) [288,5,24,65] 13 := by
  apply FastRouting.sound _ _ [288,5,24,65] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7263 c7263
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7263_3
  · exact m7263_33
  · exact m7263_34
  · exact u5369
  · exact u5370
  · exact u5371
  · exact u5372
  · exact u5373
  · exact u5374
  · exact u5375

theorem m7264_33 : Upper (D 3) (R 3) [288,5,24,66,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5365

theorem m7264_65 : Upper (D 3) (R 3) [288,5,24,66,65] 13 :=
  permutation_upper _ _ _ [288,5,24,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5370

theorem m7264_129 : Upper (D 3) (R 3) [288,5,24,66,129] 13 :=
  permutation_upper _ _ _ [288,5,24,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5373

def r7264 : Route 9 := (fun mask => (mask,id))

def c7264 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7264 : Upper (D 3) (R 3) [288,5,24,66] 13 := by
  apply FastRouting.sound _ _ [288,5,24,66] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7264 c7264
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7264_33
  · exact m7264_65
  · exact u5376
  · exact m7264_129
  · exact u5377
  · exact u5378

def b7265 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 28 104 211 227 195 195 451), lower := (rows 289 7 28 104 16 32 64 128 256), losses := [] }

theorem u7265 : Upper (D 3) (R 3) [288,5,24,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7265
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7266_3 : Upper (D 3) (R 3) [288,5,24,192,3] 13 :=
  permutation_upper _ _ _ [288,5,9,18,192] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5309

theorem m7266_33 : Upper (D 3) (R 3) [288,5,24,192,33] 13 :=
  permutation_upper _ _ _ [288,5,24,33,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5366

theorem m7266_34 : Upper (D 3) (R 3) [288,5,24,192,34] 13 :=
  permutation_upper _ _ _ [288,5,24,34,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5368

theorem m7266_65 : Upper (D 3) (R 3) [288,5,24,192,65] 13 :=
  permutation_upper _ _ _ [288,5,24,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5375

theorem m7266_66 : Upper (D 3) (R 3) [288,5,24,192,66] 13 :=
  permutation_upper _ _ _ [288,5,24,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5378

theorem m7266_96 : Upper (D 3) (R 3) [288,5,24,192,96] 13 :=
  permutation_upper _ _ _ [288,5,24,96,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5379

def r7266 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c7266 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7266 : Upper (D 3) (R 3) [288,5,24,192] 13 := by
  apply FastRouting.sound _ _ [288,5,24,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r7266 c7266
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7266_3
  · exact m7266_33
  · exact m7266_34
  · exact m7266_65
  · exact m7266_66
  · exact m7266_96
  · exact u5380

def b7267 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 26 217 233 201 201 457), lower := (rows 289 7 37 26 16 32 64 128 256), losses := [] }

theorem u7267 : Upper (D 3) (R 3) [288,5,33,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7268 : PairBound 9 := { available := 218, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 73 218 250 218 218 474), lower := (rows 289 7 37 73 16 32 64 128 256), losses := [] }

theorem u7268 : Upper (D 3) (R 3) [288,5,33,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7269 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 74 217 249 217 217 473), lower := (rows 289 7 37 74 16 32 64 128 256), losses := [] }

theorem u7269 : Upper (D 3) (R 3) [288,5,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7270 : PairBound 9 := { available := 219, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 37 200 219 251 219 219 475), lower := (rows 289 7 37 200 16 32 64 128 256), losses := [] }

theorem u7270 : Upper (D 3) (R 3) [288,5,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7271 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 73 217 249 217 217 473), lower := (rows 289 7 38 73 16 32 64 128 256), losses := [] }

theorem u7271 : Upper (D 3) (R 3) [288,5,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7271
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7272 : PairBound 9 := { available := 217, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 289 7 38 200 217 249 217 217 473), lower := (rows 289 7 38 200 16 32 64 128 256), losses := [] }

theorem u7272 : Upper (D 3) (R 3) [288,5,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7273 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 26 209 225 193 193 449), lower := (rows 289 7 44 26 16 32 64 128 256), losses := [] }

theorem u7273 : Upper (D 3) (R 3) [288,5,40,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7274 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 73 211 243 211 211 467), lower := (rows 289 7 44 73 16 32 64 128 256), losses := [] }

theorem u7274 : Upper (D 3) (R 3) [288,5,40,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7275 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 74 209 241 209 209 465), lower := (rows 289 7 44 74 16 32 64 128 256), losses := [] }

theorem u7275 : Upper (D 3) (R 3) [288,5,40,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7276 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 216, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 44 200 211 243 211 211 467), lower := (rows 289 7 44 200 16 32 64 128 256), losses := [] }

theorem u7276 : Upper (D 3) (R 3) [288,5,40,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7277 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 52 73 219 235 203 203 459), lower := (rows 289 7 52 73 16 32 64 128 256), losses := [] }

theorem u7277 : Upper (D 3) (R 3) [288,5,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7278 : PairBound 9 := { available := 201, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 52 74 217 233 201 201 457), lower := (rows 289 7 52 74 16 32 64 128 256), losses := [] }

theorem u7278 : Upper (D 3) (R 3) [288,5,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7279 : PairBound 9 := { available := 203, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 289 7 52 200 219 235 203 203 459), lower := (rows 289 7 52 200 16 32 64 128 256), losses := [] }

theorem u7279 : Upper (D 3) (R 3) [288,5,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7280 : PairBound 9 := { available := 233, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 26 249 233 233 233 489), lower := (rows 289 7 69 26 16 32 64 128 256), losses := [] }

theorem u7280 : Upper (D 3) (R 3) [288,5,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7281 : PairBound 9 := { available := 217, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 42 217 249 217 217 473), lower := (rows 289 7 69 42 16 32 64 128 256), losses := [] }

theorem u7281 : Upper (D 3) (R 3) [288,5,65,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7282 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 73 186 186 250 186 442), lower := (rows 289 7 69 73 16 32 64 128 256), losses := [] }

theorem u7282 : Upper (D 3) (R 3) [288,5,65,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7283 : PairBound 9 := { available := 185, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 74 185 185 249 185 441), lower := (rows 289 7 69 74 16 32 64 128 256), losses := [] }

theorem u7283 : Upper (D 3) (R 3) [288,5,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7284 : PairBound 9 := { available := 155, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 104 155 187 219 155 411), lower := (rows 289 7 69 104 16 32 64 128 256), losses := [] }

theorem u7284 : Upper (D 3) (R 3) [288,5,65,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7285 : PairBound 9 := { available := 250, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 137 250 250 250 250 506), lower := (rows 289 7 69 137 16 32 64 128 256), losses := [] }

theorem u7285 : Upper (D 3) (R 3) [288,5,65,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7286 : PairBound 9 := { available := 249, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 138 249 249 249 249 505), lower := (rows 289 7 69 138 16 32 64 128 256), losses := [] }

theorem u7286 : Upper (D 3) (R 3) [288,5,65,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7287 : PairBound 9 := { available := 219, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 168 219 251 219 219 475), lower := (rows 289 7 69 168 16 32 64 128 256), losses := [] }

theorem u7287 : Upper (D 3) (R 3) [288,5,65,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7288 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 2, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 69 200 187 187 251 187 443), lower := (rows 289 7 69 200 16 32 64 128 256), losses := [] }

theorem u7288 : Upper (D 3) (R 3) [288,5,65,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7288
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7289_9 : Upper (D 3) (R 3) [288,5,66,17,9] 13 :=
  permutation_upper _ _ _ [288,5,3,17,72] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5294

theorem m7289_33 : Upper (D 3) (R 3) [288,5,66,17,33] 13 :=
  permutation_upper _ _ _ [288,5,33,17,72] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5382

theorem m7289_40 : Upper (D 3) (R 3) [288,5,66,17,40] 13 :=
  permutation_upper _ _ _ [288,5,34,17,72] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5394

theorem m7289_65 : Upper (D 3) (R 3) [288,5,66,17,65] 13 :=
  permutation_upper _ _ _ [288,5,65,17,72] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5416

theorem m7289_129 : Upper (D 3) (R 3) [288,5,66,17,129] 13 :=
  permutation_upper _ _ _ [288,5,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5418

def r7289 : Route 9 := (fun mask => (mask,id))

def c7289 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7289 : Upper (D 3) (R 3) [288,5,66,17] 13 := by
  apply FastRouting.sound _ _ [288,5,66,17] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7289 c7289
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7289_9
  · exact m7289_33
  · exact m7289_40
  · exact m7289_65
  · exact u5456
  · exact u5457
  · exact m7289_129
  · exact u5458
  · exact u5459
  · exact u5460

def b7290 : PairBound 9 := { available := 217, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 41 217 249 217 217 473), lower := (rows 289 7 70 41 16 32 64 128 256), losses := [] }

theorem u7290 : Upper (D 3) (R 3) [288,5,66,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7290
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7291_9 : Upper (D 3) (R 3) [288,5,66,48,9] 13 :=
  permutation_upper _ _ _ [288,5,34,17,72] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5394

def r7291 : Route 9 := (fun mask => (mask,id))

def c7291 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7291 : Upper (D 3) (R 3) [288,5,66,48] 13 := by
  apply FastRouting.sound _ _ [288,5,66,48] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7291 c7291
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7291_9
  · exact u5463
  · exact u5464
  · exact u5465
  · exact u5466
  · exact u5467

def b7292 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 70 73 185 185 249 185 441), lower := (rows 289 7 70 73 16 32 64 128 256), losses := [] }

theorem u7292 : Upper (D 3) (R 3) [288,5,66,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7293 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 88 185 169 233 169 425), lower := (rows 289 7 70 88 16 32 64 128 256), losses := [] }

theorem u7293 : Upper (D 3) (R 3) [288,5,66,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7294 : PairBound 9 := { available := 153, camps := [{ cop := 3, region := 401, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 104 153 185 217 153 409), lower := (rows 289 7 70 104 16 32 64 128 256), losses := [] }

theorem u7294 : Upper (D 3) (R 3) [288,5,66,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7294
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7295_9 : Upper (D 3) (R 3) [288,5,66,129,9] 13 :=
  permutation_upper _ _ _ [288,5,65,17,136] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5418

theorem m7295_33 : Upper (D 3) (R 3) [288,5,66,129,33] 13 :=
  permutation_upper _ _ _ [288,5,66,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5461

theorem m7295_40 : Upper (D 3) (R 3) [288,5,66,129,40] 13 :=
  permutation_upper _ _ _ [288,5,66,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5465

theorem m7295_65 : Upper (D 3) (R 3) [288,5,66,129,65] 13 :=
  permutation_upper _ _ _ [288,5,66,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5468

theorem m7295_72 : Upper (D 3) (R 3) [288,5,66,129,72] 13 :=
  permutation_upper _ _ _ [288,5,66,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5471

theorem m7295_96 : Upper (D 3) (R 3) [288,5,66,129,96] 13 :=
  permutation_upper _ _ _ [288,5,66,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5474

def r7295 : Route 9 := (fun mask => (mask,id))

def c7295 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7295 : Upper (D 3) (R 3) [288,5,66,129] 13 := by
  apply FastRouting.sound _ _ [288,5,66,129] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7295 c7295
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7295_9
  · exact m7295_33
  · exact m7295_40
  · exact m7295_65
  · exact m7295_72
  · exact m7295_96
  · exact u5476
  · exact u5477
  · exact u5478
  · exact u5479

theorem m7296_9 : Upper (D 3) (R 3) [288,5,66,144,9] 13 :=
  permutation_upper _ _ _ [288,5,66,17,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5458

theorem m7296_33 : Upper (D 3) (R 3) [288,5,66,144,33] 13 :=
  permutation_upper _ _ _ [288,5,66,33,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5462

theorem m7296_40 : Upper (D 3) (R 3) [288,5,66,144,40] 13 :=
  permutation_upper _ _ _ [288,5,66,48,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5466

theorem m7296_65 : Upper (D 3) (R 3) [288,5,66,144,65] 13 :=
  permutation_upper _ _ _ [288,5,66,65,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5469

theorem m7296_72 : Upper (D 3) (R 3) [288,5,66,144,72] 13 :=
  permutation_upper _ _ _ [288,5,66,80,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5472

theorem m7296_96 : Upper (D 3) (R 3) [288,5,66,144,96] 13 :=
  permutation_upper _ _ _ [288,5,66,96,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5475

theorem m7296_129 : Upper (D 3) (R 3) [288,5,66,144,129] 13 :=
  permutation_upper _ _ _ [288,5,66,129,136] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5477

def r7296 : Route 9 := (fun mask => (mask,id))

def c7296 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7296 : Upper (D 3) (R 3) [288,5,66,144] 13 := by
  apply FastRouting.sound _ _ [288,5,66,144] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7296 c7296
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7296_9
  · exact m7296_33
  · exact m7296_40
  · exact m7296_65
  · exact m7296_72
  · exact m7296_96
  · exact m7296_129
  · exact u5480
  · exact u5481
  · exact u5482

theorem m7297_9 : Upper (D 3) (R 3) [288,5,66,160,9] 13 :=
  permutation_upper _ _ _ [288,5,66,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5459

theorem m7297_65 : Upper (D 3) (R 3) [288,5,66,160,65] 13 :=
  permutation_upper _ _ _ [288,5,66,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5470

theorem m7297_72 : Upper (D 3) (R 3) [288,5,66,160,72] 13 :=
  permutation_upper _ _ _ [288,5,66,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5473

theorem m7297_129 : Upper (D 3) (R 3) [288,5,66,160,129] 13 :=
  permutation_upper _ _ _ [288,5,66,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5478

theorem m7297_136 : Upper (D 3) (R 3) [288,5,66,160,136] 13 :=
  permutation_upper _ _ _ [288,5,66,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5481

def r7297 : Route 9 := (fun mask => (mask,id))

def c7297 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7297 : Upper (D 3) (R 3) [288,5,66,160] 13 := by
  apply FastRouting.sound _ _ [288,5,66,160] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7297 c7297
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7297_9
  · exact m7297_65
  · exact m7297_72
  · exact m7297_129
  · exact m7297_136
  · exact u5483

def b7298 : PairBound 9 := { available := 185, camps := [{ cop := 3, region := 305, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 70 200 185 185 249 185 441), lower := (rows 289 7 70 200 16 32 64 128 256), losses := [] }

theorem u7298 : Upper (D 3) (R 3) [288,5,66,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7298
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7299_3 : Upper (D 3) (R 3) [288,5,72,17,3] 13 :=
  permutation_upper _ _ _ [288,5,9,17,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5305

theorem m7299_33 : Upper (D 3) (R 3) [288,5,72,17,33] 13 :=
  permutation_upper _ _ _ [288,5,33,17,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5381

theorem m7299_34 : Upper (D 3) (R 3) [288,5,72,17,34] 13 :=
  permutation_upper _ _ _ [288,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5400

theorem m7299_65 : Upper (D 3) (R 3) [288,5,72,17,65] 13 :=
  permutation_upper _ _ _ [288,5,65,17,66] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5415

theorem m7299_129 : Upper (D 3) (R 3) [288,5,72,17,129] 13 :=
  permutation_upper _ _ _ [288,5,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5417

def r7299 : Route 9 := (fun mask => (mask,id))

def c7299 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7299 : Upper (D 3) (R 3) [288,5,72,17] 13 := by
  apply FastRouting.sound _ _ [288,5,72,17] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7299 c7299
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7299_3
  · exact m7299_33
  · exact m7299_34
  · exact m7299_65
  · exact u5484
  · exact u5485
  · exact m7299_129
  · exact u5486
  · exact u5487
  · exact u5488

def r7300 : Route 9 := (fun mask => (mask,id))

def c7300 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7300 : Upper (D 3) (R 3) [288,5,72,18] 13 := by
  apply FastRouting.sound _ _ [288,5,72,18] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7300 c7300
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5489
  · exact u5490
  · exact u5491
  · exact u5492
  · exact u5493
  · exact u5494

def b7301 : PairBound 9 := { available := 211, camps := [{ cop := 3, region := 214, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 41 211 243 211 211 467), lower := (rows 289 7 76 41 16 32 64 128 256), losses := [] }

theorem u7301 : Upper (D 3) (R 3) [288,5,72,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7301
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7302 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 42 209 241 209 209 465), lower := (rows 289 7 76 42 16 32 64 128 256), losses := [] }

theorem u7302 : Upper (D 3) (R 3) [288,5,72,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7302
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7303 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 56 211 227 195 195 451), lower := (rows 289 7 76 56 16 32 64 128 256), losses := [] }

theorem u7303 : Upper (D 3) (R 3) [288,5,72,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7303
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7304 : PairBound 9 := { available := 179, camps := [{ cop := 3, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 289 7 76 73 179 179 243 179 435), lower := (rows 289 7 76 73 16 32 64 128 256), losses := [] }

theorem u7304 : Upper (D 3) (R 3) [288,5,72,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7304
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7305 : PairBound 9 := { available := 177, camps := [{ cop := 2, region := 433, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 74 177 177 241 177 433), lower := (rows 289 7 76 74 16 32 64 128 256), losses := [] }

theorem u7305 : Upper (D 3) (R 3) [288,5,72,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7305
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7306 : PairBound 9 := { available := 163, camps := [{ cop := 2, region := 419, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 88 179 163 227 163 419), lower := (rows 289 7 76 88 16 32 64 128 256), losses := [] }

theorem u7306 : Upper (D 3) (R 3) [288,5,72,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7306
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7307 : PairBound 9 := { available := 147, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 104 147 179 211 147 403), lower := (rows 289 7 76 104 16 32 64 128 256), losses := [] }

theorem u7307 : Upper (D 3) (R 3) [288,5,72,96] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7307
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7308_3 : Upper (D 3) (R 3) [288,5,72,129,3] 13 :=
  permutation_upper _ _ _ [288,5,9,80,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5327

def r7308 : Route 9 := (fun mask => (mask,id))

def c7308 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7308 : Upper (D 3) (R 3) [288,5,72,129] 13 := by
  apply FastRouting.sound _ _ [288,5,72,129] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7308 c7308
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7308_3
  · exact u5519
  · exact u5520
  · exact u5521
  · exact u5522
  · exact u5523
  · exact u5524
  · exact u5525
  · exact u5526
  · exact u5527

def r7309 : Route 9 := (fun mask => (mask,id))

def c7309 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7309 : Upper (D 3) (R 3) [288,5,72,130] 13 := by
  apply FastRouting.sound _ _ [288,5,72,130] 13 (by decide) (choices 2) [33,65,96,129,160,192] r7309 c7309
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u5528
  · exact u5529
  · exact u5530
  · exact u5531
  · exact u5532
  · exact u5533

theorem m7310_3 : Upper (D 3) (R 3) [288,5,72,144,3] 13 :=
  permutation_upper _ _ _ [288,5,9,80,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5328

def r7310 : Route 9 := (fun mask => (mask,id))

def c7310 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 9 => 3 | 257 => 8 | 6 => 2 | 10 => 3 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 3 | 72 => 3 | 136 => 3 | 264 => 3 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7310 : Upper (D 3) (R 3) [288,5,72,144] 13 := by
  apply FastRouting.sound _ _ [288,5,72,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r7310 c7310
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7310_3
  · exact u5534
  · exact u5535
  · exact u5536
  · exact u5537
  · exact u5538
  · exact u5539
  · exact u5540
  · exact u5541
  · exact u5542

def b7311 : PairBound 9 := { available := 211, camps := [{ cop := 1, region := 208, targets := 32 }], pairs := [(4,5)], upper := (rows 289 7 76 168 211 243 211 211 467), lower := (rows 289 7 76 168 16 32 64 128 256), losses := [] }

theorem u7311 : Upper (D 3) (R 3) [288,5,72,160] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7311
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b7312 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 435, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 76 200 179 179 243 179 435), lower := (rows 289 7 76 200 16 32 64 128 256), losses := [] }

theorem u7312 : Upper (D 3) (R 3) [288,5,72,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7312
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7313_9 : Upper (D 3) (R 3) [288,5,80,34,9] 13 :=
  permutation_upper _ _ _ [288,5,40,17,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5400

theorem m7313_65 : Upper (D 3) (R 3) [288,5,80,34,65] 13 :=
  permutation_upper _ _ _ [288,5,72,65,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5507

theorem m7313_72 : Upper (D 3) (R 3) [288,5,80,34,72] 13 :=
  permutation_upper _ _ _ [288,5,72,80,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5513

theorem m7313_129 : Upper (D 3) (R 3) [288,5,80,34,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5520

theorem m7313_136 : Upper (D 3) (R 3) [288,5,80,34,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5535

theorem m7313_192 : Upper (D 3) (R 3) [288,5,80,34,192] 13 :=
  permutation_upper _ _ _ [288,5,72,192,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5548

def r7313 : Route 9 := (fun mask => (mask,id))

def c7313 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7313 : Upper (D 3) (R 3) [288,5,80,34] 13 := by
  apply FastRouting.sound _ _ [288,5,80,34] 13 (by decide) (choices 2) [9,65,72,129,136,192] r7313 c7313
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7313_9
  · exact m7313_65
  · exact m7313_72
  · exact m7313_129
  · exact m7313_136
  · exact m7313_192

theorem m7314_3 : Upper (D 3) (R 3) [288,5,80,65,3] 13 :=
  permutation_upper _ _ _ [288,5,9,66,65] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5321

theorem m7314_9 : Upper (D 3) (R 3) [288,5,80,65,9] 13 :=
  permutation_upper _ _ _ [288,5,65,17,66] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5415

theorem m7314_10 : Upper (D 3) (R 3) [288,5,80,65,10] 13 :=
  permutation_upper _ _ _ [288,5,72,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5490

theorem m7314_33 : Upper (D 3) (R 3) [288,5,80,65,33] 13 :=
  permutation_upper _ _ _ [288,5,72,33,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5495

theorem m7314_34 : Upper (D 3) (R 3) [288,5,80,65,34] 13 :=
  permutation_upper _ _ _ [288,5,72,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5499

theorem m7314_40 : Upper (D 3) (R 3) [288,5,80,65,40] 13 :=
  permutation_upper _ _ _ [288,5,72,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5502

theorem m7314_129 : Upper (D 3) (R 3) [288,5,80,65,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5521

theorem m7314_130 : Upper (D 3) (R 3) [288,5,80,65,130] 13 :=
  permutation_upper _ _ _ [288,5,72,130,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5529

theorem m7314_136 : Upper (D 3) (R 3) [288,5,80,65,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5536

theorem m7314_160 : Upper (D 3) (R 3) [288,5,80,65,160] 13 :=
  permutation_upper _ _ _ [288,5,72,160,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5543

def r7314 : Route 9 := (fun mask => (mask,id))

def c7314 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 65 => 6 | 257 => 8 | 6 => 2 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 72 => 6 | 264 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7314 : Upper (D 3) (R 3) [288,5,80,65] 13 := by
  apply FastRouting.sound _ _ [288,5,80,65] 13 (by decide) (choices 2) [3,9,10,33,34,40,129,130,136,160] r7314 c7314
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7314_3
  · exact m7314_9
  · exact m7314_10
  · exact m7314_33
  · exact m7314_34
  · exact m7314_40
  · exact m7314_129
  · exact m7314_130
  · exact m7314_136
  · exact m7314_160

def b7315 : PairBound 9 := { available := 169, camps := [{ cop := 3, region := 417, targets := 64 }], pairs := [(0,6)], upper := (rows 289 7 84 74 185 169 233 169 425), lower := (rows 289 7 84 74 16 32 64 128 256), losses := [] }

theorem u7315 : Upper (D 3) (R 3) [288,5,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b7315
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m7316_3 : Upper (D 3) (R 3) [288,5,80,96,3] 13 :=
  permutation_upper _ _ _ [288,5,9,66,96] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5322

theorem m7316_9 : Upper (D 3) (R 3) [288,5,80,96,9] 13 :=
  permutation_upper _ _ _ [288,5,72,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5485

theorem m7316_10 : Upper (D 3) (R 3) [288,5,80,96,10] 13 :=
  permutation_upper _ _ _ [288,5,72,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5491

theorem m7316_129 : Upper (D 3) (R 3) [288,5,80,96,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5523

theorem m7316_130 : Upper (D 3) (R 3) [288,5,80,96,130] 13 :=
  permutation_upper _ _ _ [288,5,72,130,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5530

theorem m7316_136 : Upper (D 3) (R 3) [288,5,80,96,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5538

def r7316 : Route 9 := (fun mask => (mask,id))

def c7316 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 65 => 6 | 257 => 8 | 6 => 2 | 34 => 5 | 66 => 6 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 72 => 6 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u7316 : Upper (D 3) (R 3) [288,5,80,96] 13 := by
  apply FastRouting.sound _ _ [288,5,80,96] 13 (by decide) (choices 2) [3,9,10,129,130,136] r7316 c7316
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7316_3
  · exact m7316_9
  · exact m7316_10
  · exact m7316_129
  · exact m7316_130
  · exact m7316_136

theorem m7317_3 : Upper (D 3) (R 3) [288,5,80,129,3] 13 :=
  permutation_upper _ _ _ [288,5,9,66,129] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5323

theorem m7317_9 : Upper (D 3) (R 3) [288,5,80,129,9] 13 :=
  permutation_upper _ _ _ [288,5,65,17,130] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 3 | 3 => 1 | 4 => 2 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 3 | 2 => 4 | 3 => 2 | 4 => 1 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5417

theorem m7317_10 : Upper (D 3) (R 3) [288,5,80,129,10] 13 :=
  permutation_upper _ _ _ [288,5,72,18,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5492

theorem m7317_33 : Upper (D 3) (R 3) [288,5,80,129,33] 13 :=
  permutation_upper _ _ _ [288,5,72,33,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5496

theorem m7317_34 : Upper (D 3) (R 3) [288,5,80,129,34] 13 :=
  permutation_upper _ _ _ [288,5,72,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5500

theorem m7317_40 : Upper (D 3) (R 3) [288,5,80,129,40] 13 :=
  permutation_upper _ _ _ [288,5,72,48,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5504

theorem m7317_65 : Upper (D 3) (R 3) [288,5,80,129,65] 13 :=
  permutation_upper _ _ _ [288,5,72,65,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5508

theorem m7317_66 : Upper (D 3) (R 3) [288,5,80,129,66] 13 :=
  permutation_upper _ _ _ [288,5,72,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5511

theorem m7317_72 : Upper (D 3) (R 3) [288,5,80,129,72] 13 :=
  permutation_upper _ _ _ [288,5,72,80,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5514

theorem m7317_96 : Upper (D 3) (R 3) [288,5,80,129,96] 13 :=
  permutation_upper _ _ _ [288,5,72,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5517

theorem m7317_129 : Upper (D 3) (R 3) [288,5,80,129,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5524

theorem m7317_130 : Upper (D 3) (R 3) [288,5,80,129,130] 13 :=
  permutation_upper _ _ _ [288,5,72,130,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5531

theorem m7317_136 : Upper (D 3) (R 3) [288,5,80,129,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5539

theorem m7317_160 : Upper (D 3) (R 3) [288,5,80,129,160] 13 :=
  permutation_upper _ _ _ [288,5,72,160,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5545

theorem m7317_192 : Upper (D 3) (R 3) [288,5,80,129,192] 13 :=
  permutation_upper _ _ _ [288,5,72,192,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5549

def r7317 : Route 9 := (fun mask => (mask,id))

def c7317 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7317 : Upper (D 3) (R 3) [288,5,80,129] 13 := by
  apply FastRouting.sound _ _ [288,5,80,129] 13 (by decide) (choices 2) [3,9,10,33,34,40,65,66,72,96,129,130,136,160,192] r7317 c7317
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7317_3
  · exact m7317_9
  · exact m7317_10
  · exact m7317_33
  · exact m7317_34
  · exact m7317_40
  · exact m7317_65
  · exact m7317_66
  · exact m7317_72
  · exact m7317_96
  · exact m7317_129
  · exact m7317_130
  · exact m7317_136
  · exact m7317_160
  · exact m7317_192

theorem m7318_9 : Upper (D 3) (R 3) [288,5,80,130,9] 13 :=
  permutation_upper _ _ _ [288,5,72,17,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5486

theorem m7318_33 : Upper (D 3) (R 3) [288,5,80,130,33] 13 :=
  permutation_upper _ _ _ [288,5,72,33,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5497

theorem m7318_40 : Upper (D 3) (R 3) [288,5,80,130,40] 13 :=
  permutation_upper _ _ _ [288,5,72,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5505

theorem m7318_65 : Upper (D 3) (R 3) [288,5,80,130,65] 13 :=
  permutation_upper _ _ _ [288,5,72,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5509

theorem m7318_72 : Upper (D 3) (R 3) [288,5,80,130,72] 13 :=
  permutation_upper _ _ _ [288,5,72,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5515

theorem m7318_96 : Upper (D 3) (R 3) [288,5,80,130,96] 13 :=
  permutation_upper _ _ _ [288,5,72,96,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5518

theorem m7318_129 : Upper (D 3) (R 3) [288,5,80,130,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5525

theorem m7318_136 : Upper (D 3) (R 3) [288,5,80,130,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5540

theorem m7318_160 : Upper (D 3) (R 3) [288,5,80,130,160] 13 :=
  permutation_upper _ _ _ [288,5,72,160,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5546

theorem m7318_192 : Upper (D 3) (R 3) [288,5,80,130,192] 13 :=
  permutation_upper _ _ _ [288,5,72,192,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5550

def r7318 : Route 9 := (fun mask => (mask,id))

def c7318 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 5 => 2 | 257 => 8 | 6 => 1 | 10 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 264 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7318 : Upper (D 3) (R 3) [288,5,80,130] 13 := by
  apply FastRouting.sound _ _ [288,5,80,130] 13 (by decide) (choices 2) [9,33,40,65,72,96,129,136,160,192] r7318 c7318
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7318_9
  · exact m7318_33
  · exact m7318_40
  · exact m7318_65
  · exact m7318_72
  · exact m7318_96
  · exact m7318_129
  · exact m7318_136
  · exact m7318_160
  · exact m7318_192

theorem m7319_3 : Upper (D 3) (R 3) [288,5,80,160,3] 13 :=
  permutation_upper _ _ _ [288,5,9,66,160] (fun i => match i.val with | 0 => 0 | 1 => 4 | 2 => 1 | 3 => 2 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 1 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5324

theorem m7319_9 : Upper (D 3) (R 3) [288,5,80,160,9] 13 :=
  permutation_upper _ _ _ [288,5,72,17,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5487

theorem m7319_10 : Upper (D 3) (R 3) [288,5,80,160,10] 13 :=
  permutation_upper _ _ _ [288,5,72,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5493

theorem m7319_65 : Upper (D 3) (R 3) [288,5,80,160,65] 13 :=
  permutation_upper _ _ _ [288,5,72,65,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5510

theorem m7319_66 : Upper (D 3) (R 3) [288,5,80,160,66] 13 :=
  permutation_upper _ _ _ [288,5,72,66,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5512

theorem m7319_72 : Upper (D 3) (R 3) [288,5,80,160,72] 13 :=
  permutation_upper _ _ _ [288,5,72,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5516

theorem m7319_129 : Upper (D 3) (R 3) [288,5,80,160,129] 13 :=
  permutation_upper _ _ _ [288,5,72,129,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5526

theorem m7319_130 : Upper (D 3) (R 3) [288,5,80,160,130] 13 :=
  permutation_upper _ _ _ [288,5,72,130,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5532

theorem m7319_136 : Upper (D 3) (R 3) [288,5,80,160,136] 13 :=
  permutation_upper _ _ _ [288,5,72,144,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5541

theorem m7319_192 : Upper (D 3) (R 3) [288,5,80,160,192] 13 :=
  permutation_upper _ _ _ [288,5,72,192,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u5551

def r7319 : Route 9 := (fun mask => (mask,id))

def c7319 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 33 => 5 | 257 => 8 | 6 => 2 | 34 => 5 | 258 => 8 | 12 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 40 => 5 | 264 => 8 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u7319 : Upper (D 3) (R 3) [288,5,80,160] 13 := by
  apply FastRouting.sound _ _ [288,5,80,160] 13 (by decide) (choices 2) [3,9,10,65,66,72,129,130,136,192] r7319 c7319
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m7319_3
  · exact m7319_9
  · exact m7319_10
  · exact m7319_65
  · exact m7319_66
  · exact m7319_72
  · exact m7319_129
  · exact m7319_130
  · exact m7319_136
  · exact m7319_192

#print axioms u7319
end Delivery.IrregularNine14.P03
