import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0139
import IrregularNine14P01C0140
import IrregularNine14P01C0141
import IrregularNine14P01C0142
import IrregularNine14P01C0143
import IrregularNine14P01C0144

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r9420 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9420 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9420 : Upper (D 1) (R 1) [304,5,72] 13 := by
  apply FastRouting.sound _ _ [304,5,72] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9420 c9420
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8369
  · exact u8370
  · exact u8371
  · exact u8372
  · exact u8373
  · exact u8374
  · exact u8375

def b9421 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 7 84 234 250 234 234 234 490), lower := (rows 305 7 84 8 16 32 64 128 256), losses := [] }

theorem u9421 : Upper (D 1) (R 1) [304,5,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9421
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9422 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9422 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9422 : Upper (D 1) (R 1) [304,5,192] 13 := by
  apply FastRouting.sound _ _ [304,5,192] 13 (by decide) (choices 2) [18,48,66,80,192] r9422 c9422
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u8376
  · exact u8377
  · exact u8378
  · exact u8379
  · exact u8380

def r9423 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9423 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9423 : Upper (D 1) (R 1) [304,12,3] 13 := by
  apply FastRouting.sound _ _ [304,12,3] 13 (by decide) (choices 2) [18,48,66,80,192] r9423 c9423
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u8381
  · exact u8382
  · exact u8383
  · exact u8384
  · exact u8385

def b9424 : PairBound 9 := { available := 226, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 21 234 242 226 226 226 482), lower := (rows 305 14 21 8 16 32 64 128 256), losses := [] }

theorem u9424 : Upper (D 1) (R 1) [304,12,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9424
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9425_3 : Upper (D 1) (R 1) [304,12,18,3] 13 :=
  permutation_upper _ _ _ [304,12,3,18] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8381

theorem m9425_33 : Upper (D 1) (R 1) [304,12,18,33] 13 :=
  permutation_upper _ _ _ [304,12,17,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8386

def r9425 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9425 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9425 : Upper (D 1) (R 1) [304,12,18] 13 := by
  apply FastRouting.sound _ _ [304,12,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9425 c9425
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9425_3
  · exact m9425_33
  · exact u8390
  · exact u8391
  · exact u8392
  · exact u8393
  · exact u8394

def b9426 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 14 52 203 211 227 195 195 451), lower := (rows 305 14 52 8 16 32 64 128 256), losses := [] }

theorem u9426 : Upper (D 1) (R 1) [304,12,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9426
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9427_18 : Upper (D 1) (R 1) [304,12,65,18] 13 :=
  permutation_upper _ _ _ [304,12,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8391

theorem m9427_48 : Upper (D 1) (R 1) [304,12,65,48] 13 :=
  permutation_upper _ _ _ [304,12,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8395

def r9427 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9427 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9427 : Upper (D 1) (R 1) [304,12,65] 13 := by
  apply FastRouting.sound _ _ [304,12,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9427 c9427
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9427_18
  · exact m9427_48
  · exact u8398
  · exact u8399
  · exact u8400
  · exact u8401
  · exact u8402

theorem m9428_3 : Upper (D 1) (R 1) [304,12,66,3] 13 :=
  permutation_upper _ _ _ [304,12,3,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8383

theorem m9428_17 : Upper (D 1) (R 1) [304,12,66,17] 13 :=
  permutation_upper _ _ _ [304,12,17,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8387

theorem m9428_18 : Upper (D 1) (R 1) [304,12,66,18] 13 :=
  permutation_upper _ _ _ [304,12,18,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8392

theorem m9428_48 : Upper (D 1) (R 1) [304,12,66,48] 13 :=
  permutation_upper _ _ _ [304,12,48,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8396

theorem m9428_65 : Upper (D 1) (R 1) [304,12,66,65] 13 :=
  permutation_upper _ _ _ [304,12,65,66] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8398

theorem m9428_129 : Upper (D 1) (R 1) [304,12,66,129] 13 :=
  permutation_upper _ _ _ [304,12,65,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8400

def r9428 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9428 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9428 : Upper (D 1) (R 1) [304,12,66] 13 := by
  apply FastRouting.sound _ _ [304,12,66] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9428 c9428
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9428_3
  · exact m9428_17
  · exact m9428_18
  · exact m9428_48
  · exact m9428_65
  · exact u8403
  · exact u8404
  · exact m9428_129
  · exact u8405
  · exact u8406
  · exact u8407

theorem m9429_3 : Upper (D 1) (R 1) [304,12,80,3] 13 :=
  permutation_upper _ _ _ [304,12,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8384

theorem m9429_33 : Upper (D 1) (R 1) [304,12,80,33] 13 :=
  permutation_upper _ _ _ [304,12,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8388

theorem m9429_34 : Upper (D 1) (R 1) [304,12,80,34] 13 :=
  permutation_upper _ _ _ [304,12,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8393

theorem m9429_65 : Upper (D 1) (R 1) [304,12,80,65] 13 :=
  permutation_upper _ _ _ [304,12,65,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8399

theorem m9429_66 : Upper (D 1) (R 1) [304,12,80,66] 13 :=
  permutation_upper _ _ _ [304,12,66,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8404

theorem m9429_129 : Upper (D 1) (R 1) [304,12,80,129] 13 :=
  permutation_upper _ _ _ [304,12,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8401

theorem m9429_130 : Upper (D 1) (R 1) [304,12,80,130] 13 :=
  permutation_upper _ _ _ [304,12,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8406

def r9429 : Route 9 := (fun mask => (mask,id))

def c9429 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9429 : Upper (D 1) (R 1) [304,12,80] 13 := by
  apply FastRouting.sound _ _ [304,12,80] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9429 c9429
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9429_3
  · exact m9429_33
  · exact m9429_34
  · exact m9429_65
  · exact m9429_66
  · exact u8408
  · exact m9429_129
  · exact m9429_130
  · exact u8409
  · exact u8410

theorem m9430_3 : Upper (D 1) (R 1) [304,12,192,3] 13 :=
  permutation_upper _ _ _ [304,12,3,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8385

theorem m9430_17 : Upper (D 1) (R 1) [304,12,192,17] 13 :=
  permutation_upper _ _ _ [304,12,17,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8389

theorem m9430_18 : Upper (D 1) (R 1) [304,12,192,18] 13 :=
  permutation_upper _ _ _ [304,12,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8394

theorem m9430_48 : Upper (D 1) (R 1) [304,12,192,48] 13 :=
  permutation_upper _ _ _ [304,12,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8397

theorem m9430_65 : Upper (D 1) (R 1) [304,12,192,65] 13 :=
  permutation_upper _ _ _ [304,12,65,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8402

theorem m9430_66 : Upper (D 1) (R 1) [304,12,192,66] 13 :=
  permutation_upper _ _ _ [304,12,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8407

theorem m9430_80 : Upper (D 1) (R 1) [304,12,192,80] 13 :=
  permutation_upper _ _ _ [304,12,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8410

def r9430 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9430 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9430 : Upper (D 1) (R 1) [304,12,192] 13 := by
  apply FastRouting.sound _ _ [304,12,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r9430 c9430
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9430_3
  · exact m9430_17
  · exact m9430_18
  · exact m9430_48
  · exact m9430_65
  · exact m9430_66
  · exact m9430_80
  · exact u8411

def b9431 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 6, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 7 234 250 234 234 234 490), lower := (rows 305 22 7 8 16 32 64 128 256), losses := [] }

theorem u9431 : Upper (D 1) (R 1) [304,20,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9431
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9432 : PairBound 9 := { available := 226, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 13 234 242 226 226 226 482), lower := (rows 305 22 13 8 16 32 64 128 256), losses := [] }

theorem u9432 : Upper (D 1) (R 1) [304,20,9] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9432
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9433 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9433 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9433 : Upper (D 1) (R 1) [304,20,10] 13 := by
  apply FastRouting.sound _ _ [304,20,10] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9433 c9433
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8412
  · exact u8413
  · exact u8414
  · exact u8415
  · exact u8416
  · exact u8417
  · exact u8418

def b9434 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 37 202 218 234 202 202 458), lower := (rows 305 22 37 8 16 32 64 128 256), losses := [] }

theorem u9434 : Upper (D 1) (R 1) [304,20,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9434
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9435 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 6, targets := 64 }], pairs := [(1,6)], upper := (rows 305 22 38 203 219 235 203 203 459), lower := (rows 305 22 38 8 16 32 64 128 256), losses := [] }

theorem u9435 : Upper (D 1) (R 1) [304,20,34] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9435
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9436 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9436 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9436 : Upper (D 1) (R 1) [304,20,40] 13 := by
  apply FastRouting.sound _ _ [304,20,40] 13 (by decide) (choices 2) [3,65,66,192] r9436 c9436
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u8419
  · exact u8420
  · exact u8421
  · exact u8422

def b9437 : PairBound 9 := { available := 234, camps := [{ cop := 1, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 22 69 234 250 234 234 234 490), lower := (rows 305 22 69 8 16 32 64 128 256), losses := [] }

theorem u9437 : Upper (D 1) (R 1) [304,20,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9437
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9438 : Route 9 := (fun mask => (mask,id))

def c9438 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9438 : Upper (D 1) (R 1) [304,20,66] 13 := by
  apply FastRouting.sound _ _ [304,20,66] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9438 c9438
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8423
  · exact u8424
  · exact u8425
  · exact u8426
  · exact u8427
  · exact u8428
  · exact u8429
  · exact u8430
  · exact u8431
  · exact u8432

def r9439 : Route 9 := (fun mask => (mask,id))

def c9439 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9439 : Upper (D 1) (R 1) [304,20,72] 13 := by
  apply FastRouting.sound _ _ [304,20,72] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9439 c9439
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8433
  · exact u8434
  · exact u8435
  · exact u8436
  · exact u8437
  · exact u8438
  · exact u8439
  · exact u8440
  · exact u8441
  · exact u8442

def r9440 : Route 9 := (fun mask => (mask,id))

def c9440 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 33 => 5 | 257 => 8 | 6 => 2 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9440 : Upper (D 1) (R 1) [304,20,96] 13 := by
  apply FastRouting.sound _ _ [304,20,96] 13 (by decide) (choices 2) [3,65,66,129,130,192] r9440 c9440
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8443
  · exact u8444
  · exact u8445
  · exact u8446
  · exact u8447
  · exact u8448

def r9441 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c9441 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9441 : Upper (D 1) (R 1) [304,20,192] 13 := by
  apply FastRouting.sound _ _ [304,20,192] 13 (by decide) (choices 2) [3,33,34,65,66,96,192] r9441 c9441
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8449
  · exact u8450
  · exact u8451
  · exact u8452
  · exact u8453
  · exact u8454
  · exact u8455

def r9442 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9442 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9442 : Upper (D 1) (R 1) [304,65,10] 13 := by
  apply FastRouting.sound _ _ [304,65,10] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r9442 c9442
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8456
  · exact u8457
  · exact u8458
  · exact u8459
  · exact u8460
  · exact u8461
  · exact u8462
  · exact u8463
  · exact u8464
  · exact u8465
  · exact u8466

def b9443 : PairBound 9 := { available := 238, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 67 22 238 254 238 238 238 494), lower := (rows 305 67 22 8 16 32 64 128 256), losses := [] }

theorem u9443 : Upper (D 1) (R 1) [304,65,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9443
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9444_6 : Upper (D 1) (R 1) [304,65,24,6] 13 :=
  permutation_upper _ _ _ [304,65,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8458

theorem m9444_34 : Upper (D 1) (R 1) [304,65,24,34] 13 :=
  permutation_upper _ _ _ [304,65,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8467

def r9444 : Route 9 := (fun mask => (mask,id))

def c9444 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9444 : Upper (D 1) (R 1) [304,65,24] 13 := by
  apply FastRouting.sound _ _ [304,65,24] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r9444 c9444
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9444_6
  · exact m9444_34
  · exact u8474
  · exact u8475
  · exact u8476
  · exact u8477
  · exact u8478
  · exact u8479
  · exact u8480
  · exact u8481

def b9445 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 52 206 222 238 206 206 462), lower := (rows 305 67 52 8 16 32 64 128 256), losses := [] }

theorem u9445 : Upper (D 1) (R 1) [304,65,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9445
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9446 : PairBound 9 := { available := 190, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 67 70 190 190 190 254 190 446), lower := (rows 305 67 70 8 16 32 64 128 256), losses := [] }

theorem u9446 : Upper (D 1) (R 1) [304,65,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9446
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9447_6 : Upper (D 1) (R 1) [304,65,72,6] 13 :=
  permutation_upper _ _ _ [304,65,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8461

theorem m9447_18 : Upper (D 1) (R 1) [304,65,72,18] 13 :=
  permutation_upper _ _ _ [304,65,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8468

theorem m9447_20 : Upper (D 1) (R 1) [304,65,72,20] 13 :=
  permutation_upper _ _ _ [304,65,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8476

theorem m9447_48 : Upper (D 1) (R 1) [304,65,72,48] 13 :=
  permutation_upper _ _ _ [304,65,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8482

def r9447 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9447 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9447 : Upper (D 1) (R 1) [304,65,72] 13 := by
  apply FastRouting.sound _ _ [304,65,72] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r9447 c9447
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9447_6
  · exact m9447_18
  · exact m9447_20
  · exact m9447_48
  · exact u8489
  · exact u8490
  · exact u8491

theorem m9448_6 : Upper (D 1) (R 1) [304,65,80,6] 13 :=
  permutation_upper _ _ _ [304,65,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8462

theorem m9448_34 : Upper (D 1) (R 1) [304,65,80,34] 13 :=
  permutation_upper _ _ _ [304,65,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8469

theorem m9448_36 : Upper (D 1) (R 1) [304,65,80,36] 13 :=
  permutation_upper _ _ _ [304,65,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8477

def r9448 : Route 9 := (fun mask => (mask,id))

def c9448 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9448 : Upper (D 1) (R 1) [304,65,80] 13 := by
  apply FastRouting.sound _ _ [304,65,80] 13 (by decide) (choices 2) [6,34,36,130,132,160] r9448 c9448
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9448_6
  · exact m9448_34
  · exact m9448_36
  · exact u8492
  · exact u8493
  · exact u8494

theorem m9449_6 : Upper (D 1) (R 1) [304,65,130,6] 13 :=
  permutation_upper _ _ _ [304,65,10,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8463

theorem m9449_18 : Upper (D 1) (R 1) [304,65,130,18] 13 :=
  permutation_upper _ _ _ [304,65,18,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8470

theorem m9449_20 : Upper (D 1) (R 1) [304,65,130,20] 13 :=
  permutation_upper _ _ _ [304,65,24,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8478

theorem m9449_48 : Upper (D 1) (R 1) [304,65,130,48] 13 :=
  permutation_upper _ _ _ [304,65,48,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8483

theorem m9449_66 : Upper (D 1) (R 1) [304,65,130,66] 13 :=
  permutation_upper _ _ _ [304,65,66,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8486

theorem m9449_68 : Upper (D 1) (R 1) [304,65,130,68] 13 :=
  permutation_upper _ _ _ [304,65,72,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8489

theorem m9449_80 : Upper (D 1) (R 1) [304,65,130,80] 13 :=
  permutation_upper _ _ _ [304,65,80,130] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8492

def r9449 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9449 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9449 : Upper (D 1) (R 1) [304,65,130] 13 := by
  apply FastRouting.sound _ _ [304,65,130] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r9449 c9449
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9449_6
  · exact m9449_18
  · exact m9449_20
  · exact m9449_48
  · exact m9449_66
  · exact m9449_68
  · exact m9449_80
  · exact u8495
  · exact u8496
  · exact u8497
  · exact u8498

theorem m9450_6 : Upper (D 1) (R 1) [304,65,136,6] 13 :=
  permutation_upper _ _ _ [304,65,10,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8464

theorem m9450_18 : Upper (D 1) (R 1) [304,65,136,18] 13 :=
  permutation_upper _ _ _ [304,65,18,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8471

theorem m9450_20 : Upper (D 1) (R 1) [304,65,136,20] 13 :=
  permutation_upper _ _ _ [304,65,24,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8479

theorem m9450_48 : Upper (D 1) (R 1) [304,65,136,48] 13 :=
  permutation_upper _ _ _ [304,65,48,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8484

theorem m9450_66 : Upper (D 1) (R 1) [304,65,136,66] 13 :=
  permutation_upper _ _ _ [304,65,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8487

theorem m9450_68 : Upper (D 1) (R 1) [304,65,136,68] 13 :=
  permutation_upper _ _ _ [304,65,72,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8490

theorem m9450_80 : Upper (D 1) (R 1) [304,65,136,80] 13 :=
  permutation_upper _ _ _ [304,65,80,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8493

theorem m9450_130 : Upper (D 1) (R 1) [304,65,136,130] 13 :=
  permutation_upper _ _ _ [304,65,130,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8496

def r9450 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9450 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9450 : Upper (D 1) (R 1) [304,65,136] 13 := by
  apply FastRouting.sound _ _ [304,65,136] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r9450 c9450
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9450_6
  · exact m9450_18
  · exact m9450_20
  · exact m9450_48
  · exact m9450_66
  · exact m9450_68
  · exact m9450_80
  · exact m9450_130
  · exact u8499
  · exact u8500
  · exact u8501

theorem m9451_6 : Upper (D 1) (R 1) [304,65,144,6] 13 :=
  permutation_upper _ _ _ [304,65,10,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8465

theorem m9451_34 : Upper (D 1) (R 1) [304,65,144,34] 13 :=
  permutation_upper _ _ _ [304,65,18,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8472

theorem m9451_36 : Upper (D 1) (R 1) [304,65,144,36] 13 :=
  permutation_upper _ _ _ [304,65,24,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8480

theorem m9451_66 : Upper (D 1) (R 1) [304,65,144,66] 13 :=
  permutation_upper _ _ _ [304,65,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8488

theorem m9451_68 : Upper (D 1) (R 1) [304,65,144,68] 13 :=
  permutation_upper _ _ _ [304,65,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8491

theorem m9451_96 : Upper (D 1) (R 1) [304,65,144,96] 13 :=
  permutation_upper _ _ _ [304,65,80,160] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8494

theorem m9451_130 : Upper (D 1) (R 1) [304,65,144,130] 13 :=
  permutation_upper _ _ _ [304,65,130,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8497

theorem m9451_132 : Upper (D 1) (R 1) [304,65,144,132] 13 :=
  permutation_upper _ _ _ [304,65,136,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8500

def r9451 : Route 9 := (fun mask => (mask,id))

def c9451 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9451 : Upper (D 1) (R 1) [304,65,144] 13 := by
  apply FastRouting.sound _ _ [304,65,144] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r9451 c9451
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9451_6
  · exact m9451_34
  · exact m9451_36
  · exact m9451_66
  · exact m9451_68
  · exact m9451_96
  · exact m9451_130
  · exact m9451_132
  · exact u8502
  · exact u8503

theorem m9452_6 : Upper (D 1) (R 1) [304,65,192,6] 13 :=
  permutation_upper _ _ _ [304,65,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8466

theorem m9452_18 : Upper (D 1) (R 1) [304,65,192,18] 13 :=
  permutation_upper _ _ _ [304,65,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8473

theorem m9452_20 : Upper (D 1) (R 1) [304,65,192,20] 13 :=
  permutation_upper _ _ _ [304,65,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8481

theorem m9452_48 : Upper (D 1) (R 1) [304,65,192,48] 13 :=
  permutation_upper _ _ _ [304,65,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8485

theorem m9452_130 : Upper (D 1) (R 1) [304,65,192,130] 13 :=
  permutation_upper _ _ _ [304,65,130,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8498

theorem m9452_132 : Upper (D 1) (R 1) [304,65,192,132] 13 :=
  permutation_upper _ _ _ [304,65,136,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8501

theorem m9452_144 : Upper (D 1) (R 1) [304,65,192,144] 13 :=
  permutation_upper _ _ _ [304,65,144,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8503

def r9452 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9452 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9452 : Upper (D 1) (R 1) [304,65,192] 13 := by
  apply FastRouting.sound _ _ [304,65,192] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r9452 c9452
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9452_6
  · exact m9452_18
  · exact m9452_20
  · exact m9452_48
  · exact m9452_130
  · exact m9452_132
  · exact m9452_144

def r9453 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9453 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9453 : Upper (D 1) (R 1) [304,68,3] 13 := by
  apply FastRouting.sound _ _ [304,68,3] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9453 c9453
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8504
  · exact u8505
  · exact u8506
  · exact u8507
  · exact u8508
  · exact u8509
  · exact u8510

def r9454 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9454 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9454 : Upper (D 1) (R 1) [304,68,9] 13 := by
  apply FastRouting.sound _ _ [304,68,9] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9454 c9454
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8511
  · exact u8512
  · exact u8513
  · exact u8514
  · exact u8515
  · exact u8516
  · exact u8517

def r9455 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9455 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9455 : Upper (D 1) (R 1) [304,68,10] 13 := by
  apply FastRouting.sound _ _ [304,68,10] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9455 c9455
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8518
  · exact u8519
  · exact u8520
  · exact u8521
  · exact u8522
  · exact u8523
  · exact u8524
  · exact u8525
  · exact u8526
  · exact u8527
  · exact u8528

def b9456 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 21 234 250 234 234 234 490), lower := (rows 305 70 21 8 16 32 64 128 256), losses := [] }

theorem u9456 : Upper (D 1) (R 1) [304,68,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9456
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9457 : Route 9 := (fun mask => (mask,id))

def c9457 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9457 : Upper (D 1) (R 1) [304,68,18] 13 := by
  apply FastRouting.sound _ _ [304,68,18] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9457 c9457
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8529
  · exact u8530
  · exact u8531
  · exact u8532
  · exact u8533
  · exact u8534
  · exact u8535
  · exact u8536
  · exact u8537
  · exact u8538

def r9458 : Route 9 := (fun mask => (mask,id))

def c9458 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9458 : Upper (D 1) (R 1) [304,68,24] 13 := by
  apply FastRouting.sound _ _ [304,68,24] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9458 c9458
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8539
  · exact u8540
  · exact u8541
  · exact u8542
  · exact u8543
  · exact u8544
  · exact u8545
  · exact u8546
  · exact u8547
  · exact u8548

def b9459 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 70 52 203 219 235 203 203 459), lower := (rows 305 70 52 8 16 32 64 128 256), losses := [] }

theorem u9459 : Upper (D 1) (R 1) [304,68,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9459
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9460 : PairBound 9 := { available := 186, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 69 186 186 186 250 186 442), lower := (rows 305 70 69 8 16 32 64 128 256), losses := [] }

theorem u9460 : Upper (D 1) (R 1) [304,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9460
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9461 : PairBound 9 := { available := 187, camps := [{ cop := 6, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 70 187 187 187 251 187 443), lower := (rows 305 70 70 8 16 32 64 128 256), losses := [] }

theorem u9461 : Upper (D 1) (R 1) [304,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9461
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9462 : PairBound 9 := { available := 179, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 76 187 179 179 243 179 435), lower := (rows 305 70 76 8 16 32 64 128 256), losses := [] }

theorem u9462 : Upper (D 1) (R 1) [304,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9462
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9463 : PairBound 9 := { available := 171, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 84 171 187 171 235 171 427), lower := (rows 305 70 84 8 16 32 64 128 256), losses := [] }

theorem u9463 : Upper (D 1) (R 1) [304,68,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9463
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9464 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9464 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9464 : Upper (D 1) (R 1) [304,68,129] 13 := by
  apply FastRouting.sound _ _ [304,68,129] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r9464 c9464
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8549
  · exact u8550
  · exact u8551
  · exact u8552
  · exact u8553
  · exact u8554
  · exact u8555

def r9465 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9465 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9465 : Upper (D 1) (R 1) [304,68,130] 13 := by
  apply FastRouting.sound _ _ [304,68,130] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9465 c9465
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8556
  · exact u8557
  · exact u8558
  · exact u8559
  · exact u8560
  · exact u8561
  · exact u8562
  · exact u8563
  · exact u8564
  · exact u8565
  · exact u8566

def r9466 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c9466 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9466 : Upper (D 1) (R 1) [304,68,136] 13 := by
  apply FastRouting.sound _ _ [304,68,136] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r9466 c9466
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8567
  · exact u8568
  · exact u8569
  · exact u8570
  · exact u8571
  · exact u8572
  · exact u8573
  · exact u8574
  · exact u8575
  · exact u8576
  · exact u8577

def r9467 : Route 9 := (fun mask => (mask,id))

def c9467 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 17 => 4 | 257 => 8 | 6 => 2 | 18 => 4 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9467 : Upper (D 1) (R 1) [304,68,144] 13 := by
  apply FastRouting.sound _ _ [304,68,144] 13 (by decide) (choices 2) [3,33,34,65,66,96,129,130,160,192] r9467 c9467
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8578
  · exact u8579
  · exact u8580
  · exact u8581
  · exact u8582
  · exact u8583
  · exact u8584
  · exact u8585
  · exact u8586
  · exact u8587

def b9468 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 196 187 187 187 251 187 443), lower := (rows 305 70 196 8 16 32 64 128 256), losses := [] }

theorem u9468 : Upper (D 1) (R 1) [304,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9468
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b9469 : PairBound 9 := { available := 238, camps := [{ cop := 2, region := 232, targets := 16 }], pairs := [(3,4)], upper := (rows 305 82 7 238 254 238 238 238 494), lower := (rows 305 82 7 8 16 32 64 128 256), losses := [] }

theorem u9469 : Upper (D 1) (R 1) [304,80,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9469
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r9470 : Route 9 := (fun mask => (mask,id))

def c9470 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9470 : Upper (D 1) (R 1) [304,80,9] 13 := by
  apply FastRouting.sound _ _ [304,80,9] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r9470 c9470
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u8597
  · exact u8598
  · exact u8599
  · exact u8600
  · exact u8601
  · exact u8602
  · exact u8603
  · exact u8604
  · exact u8605
  · exact u8606

theorem m9471_3 : Upper (D 1) (R 1) [304,80,10,3] 13 :=
  permutation_upper _ _ _ [304,80,3,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8588

theorem m9471_5 : Upper (D 1) (R 1) [304,80,10,5] 13 :=
  permutation_upper _ _ _ [304,80,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8597

def r9471 : Route 9 := (fun mask => (mask,id))

def c9471 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9471 : Upper (D 1) (R 1) [304,80,10] 13 := by
  apply FastRouting.sound _ _ [304,80,10] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r9471 c9471
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9471_3
  · exact m9471_5
  · exact u8607
  · exact u8608
  · exact u8609
  · exact u8610
  · exact u8611
  · exact u8612
  · exact u8613
  · exact u8614
  · exact u8615
  · exact u8616
  · exact u8617
  · exact u8618
  · exact u8619

def b9472 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 305 82 37 206 222 238 206 206 462), lower := (rows 305 82 37 8 16 32 64 128 256), losses := [] }

theorem u9472 : Upper (D 1) (R 1) [304,80,33] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9472
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9473_3 : Upper (D 1) (R 1) [304,80,34,3] 13 :=
  permutation_upper _ _ _ [304,80,3,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8589

theorem m9473_5 : Upper (D 1) (R 1) [304,80,34,5] 13 :=
  permutation_upper _ _ _ [304,80,9,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8598

theorem m9473_6 : Upper (D 1) (R 1) [304,80,34,6] 13 :=
  permutation_upper _ _ _ [304,80,10,34] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8609

def r9473 : Route 9 := (fun mask => (mask,id))

def c9473 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9473 : Upper (D 1) (R 1) [304,80,34] 13 := by
  apply FastRouting.sound _ _ [304,80,34] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9473 c9473
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9473_3
  · exact m9473_5
  · exact m9473_6
  · exact u8624
  · exact u8625
  · exact u8626
  · exact u8627
  · exact u8628
  · exact u8629
  · exact u8630

theorem m9474_3 : Upper (D 1) (R 1) [304,80,40,3] 13 :=
  permutation_upper _ _ _ [304,80,3,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8590

theorem m9474_5 : Upper (D 1) (R 1) [304,80,40,5] 13 :=
  permutation_upper _ _ _ [304,80,9,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8599

theorem m9474_6 : Upper (D 1) (R 1) [304,80,40,6] 13 :=
  permutation_upper _ _ _ [304,80,10,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8610

def r9474 : Route 9 := (fun mask => (mask,id))

def c9474 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 257 => 8 | 18 => 4 | 34 => 5 | 258 => 8 | 20 => 4 | 36 => 5 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9474 : Upper (D 1) (R 1) [304,80,40] 13 := by
  apply FastRouting.sound _ _ [304,80,40] 13 (by decide) (choices 2) [3,5,6,65,66,68,129,130,132,192] r9474 c9474
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9474_3
  · exact m9474_5
  · exact m9474_6
  · exact u8631
  · exact u8632
  · exact u8633
  · exact u8634
  · exact u8635
  · exact u8636
  · exact u8637

theorem m9475_6 : Upper (D 1) (R 1) [304,80,65,6] 13 :=
  permutation_upper _ _ _ [304,80,10,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8611

theorem m9475_34 : Upper (D 1) (R 1) [304,80,65,34] 13 :=
  permutation_upper _ _ _ [304,80,34,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8624

theorem m9475_36 : Upper (D 1) (R 1) [304,80,65,36] 13 :=
  permutation_upper _ _ _ [304,80,40,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8631

def r9475 : Route 9 := (fun mask => (mask,id))

def c9475 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9475 : Upper (D 1) (R 1) [304,80,65] 13 := by
  apply FastRouting.sound _ _ [304,80,65] 13 (by decide) (choices 2) [6,34,36,130,132,160] r9475 c9475
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9475_6
  · exact m9475_34
  · exact m9475_36
  · exact u8638
  · exact u8639
  · exact u8640

def b9476 : PairBound 9 := { available := 175, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 305 82 70 175 191 175 239 175 431), lower := (rows 305 82 70 8 16 32 64 128 256), losses := [] }

theorem u9476 : Upper (D 1) (R 1) [304,80,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b9476
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m9477_3 : Upper (D 1) (R 1) [304,80,72,3] 13 :=
  permutation_upper _ _ _ [304,80,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8591

theorem m9477_5 : Upper (D 1) (R 1) [304,80,72,5] 13 :=
  permutation_upper _ _ _ [304,80,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8601

theorem m9477_6 : Upper (D 1) (R 1) [304,80,72,6] 13 :=
  permutation_upper _ _ _ [304,80,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8613

theorem m9477_33 : Upper (D 1) (R 1) [304,80,72,33] 13 :=
  permutation_upper _ _ _ [304,80,33,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8620

theorem m9477_34 : Upper (D 1) (R 1) [304,80,72,34] 13 :=
  permutation_upper _ _ _ [304,80,34,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8626

theorem m9477_36 : Upper (D 1) (R 1) [304,80,72,36] 13 :=
  permutation_upper _ _ _ [304,80,40,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8633

def r9477 : Route 9 := (fun mask => (mask,id))

def c9477 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 257 => 8 | 18 => 4 | 66 => 6 | 258 => 8 | 20 => 4 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9477 : Upper (D 1) (R 1) [304,80,72] 13 := by
  apply FastRouting.sound _ _ [304,80,72] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160] r9477 c9477
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9477_3
  · exact m9477_5
  · exact m9477_6
  · exact m9477_33
  · exact m9477_34
  · exact m9477_36
  · exact u8645
  · exact u8646
  · exact u8647
  · exact u8648

theorem m9478_3 : Upper (D 1) (R 1) [304,80,96,3] 13 :=
  permutation_upper _ _ _ [304,80,3,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8592

theorem m9478_5 : Upper (D 1) (R 1) [304,80,96,5] 13 :=
  permutation_upper _ _ _ [304,80,9,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8602

theorem m9478_6 : Upper (D 1) (R 1) [304,80,96,6] 13 :=
  permutation_upper _ _ _ [304,80,10,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8614

def r9478 : Route 9 := (fun mask => (mask,id))

def c9478 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 33 => 5 | 65 => 6 | 257 => 8 | 18 => 4 | 34 => 5 | 66 => 6 | 258 => 8 | 20 => 4 | 36 => 5 | 68 => 6 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 5 | 160 => 5 | 288 => 5 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u9478 : Upper (D 1) (R 1) [304,80,96] 13 := by
  apply FastRouting.sound _ _ [304,80,96] 13 (by decide) (choices 2) [3,5,6,129,130,132] r9478 c9478
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9478_3
  · exact m9478_5
  · exact m9478_6
  · exact u8649
  · exact u8650
  · exact u8651

theorem m9479_6 : Upper (D 1) (R 1) [304,80,129,6] 13 :=
  permutation_upper _ _ _ [304,80,10,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8615

theorem m9479_34 : Upper (D 1) (R 1) [304,80,129,34] 13 :=
  permutation_upper _ _ _ [304,80,34,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8627

theorem m9479_36 : Upper (D 1) (R 1) [304,80,129,36] 13 :=
  permutation_upper _ _ _ [304,80,40,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8634

theorem m9479_66 : Upper (D 1) (R 1) [304,80,129,66] 13 :=
  permutation_upper _ _ _ [304,80,66,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8641

theorem m9479_68 : Upper (D 1) (R 1) [304,80,129,68] 13 :=
  permutation_upper _ _ _ [304,80,72,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8645

theorem m9479_96 : Upper (D 1) (R 1) [304,80,129,96] 13 :=
  permutation_upper _ _ _ [304,80,96,129] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u8649

def r9479 : Route 9 := (fun mask => (mask,id))

def c9479 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u9479 : Upper (D 1) (R 1) [304,80,129] 13 := by
  apply FastRouting.sound _ _ [304,80,129] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r9479 c9479
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m9479_6
  · exact m9479_34
  · exact m9479_36
  · exact m9479_66
  · exact m9479_68
  · exact m9479_96
  · exact u8652
  · exact u8653
  · exact u8654
  · exact u8655

#print axioms u9479
end Delivery.IrregularNine14.P01
