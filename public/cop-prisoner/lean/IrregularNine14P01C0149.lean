import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0107
import IrregularNine14P01C0108
import IrregularNine14P01C0109
import IrregularNine14P01C0110
import IrregularNine14P01C0111
import IrregularNine14P01C0112

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b8940 : PairBound 9 := { available := 442, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 69 442 442 442 506 442 442), lower := (rows 51 70 69 8 16 32 64 128 256), losses := [] }

theorem u8940 : Upper (D 1) (R 1) [50,68,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8940
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8941 : PairBound 9 := { available := 441, camps := [{ cop := 6, region := 6, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 70 441 441 441 505 441 441), lower := (rows 51 70 70 8 16 32 64 128 256), losses := [] }

theorem u8941 : Upper (D 1) (R 1) [50,68,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8941
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8942 : PairBound 9 := { available := 435, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 76 443 435 435 499 435 435), lower := (rows 51 70 76 8 16 32 64 128 256), losses := [] }

theorem u8942 : Upper (D 1) (R 1) [50,68,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8942
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8943 : PairBound 9 := { available := 427, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 84 427 443 427 491 427 427), lower := (rows 51 70 84 8 16 32 64 128 256), losses := [] }

theorem u8943 : Upper (D 1) (R 1) [50,68,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8943
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8944 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8944 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8944 : Upper (D 1) (R 1) [50,68,129] 13 := by
  apply FastRouting.sound _ _ [50,68,129] 13 (by decide) (choices 2) [18,48,66,80,130,144,192,258,272,320,384] r8944 c8944
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6455
  · exact u6456
  · exact u6457
  · exact u6458
  · exact u6459
  · exact u6460
  · exact u6461
  · exact u6462
  · exact u6463
  · exact u6464
  · exact u6465

def b8945 : PairBound 9 := { available := 505, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 134 505 505 505 505 505 505), lower := (rows 51 70 134 8 16 32 64 128 256), losses := [] }

theorem u8945 : Upper (D 1) (R 1) [50,68,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8945
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8946 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8946 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 6 => 2 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | _ => 0)

theorem u8946 : Upper (D 1) (R 1) [50,68,136] 13 := by
  apply FastRouting.sound _ _ [50,68,136] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192,257,258,272,320,384] r8946 c8946
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6466
  · exact u6467
  · exact u6468
  · exact u6469
  · exact u6470
  · exact u6471
  · exact u6472
  · exact u6473
  · exact u6474
  · exact u6475
  · exact u6476
  · exact u6477
  · exact u6478
  · exact u6479
  · exact u6480
  · exact u6481

def b8947 : PairBound 9 := { available := 491, camps := [{ cop := 0, region := 456, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 148 491 507 491 491 491 491), lower := (rows 51 70 148 8 16 32 64 128 256), losses := [] }

theorem u8947 : Upper (D 1) (R 1) [50,68,144] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8947
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8948 : PairBound 9 := { available := 443, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 196 443 443 443 507 443 443), lower := (rows 51 70 196 8 16 32 64 128 256), losses := [] }

theorem u8948 : Upper (D 1) (R 1) [50,68,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8948
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8949 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8949 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8949 : Upper (D 1) (R 1) [50,68,257] 13 := by
  apply FastRouting.sound _ _ [50,68,257] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r8949 c8949
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6482
  · exact u6483
  · exact u6484
  · exact u6485
  · exact u6486
  · exact u6487
  · exact u6488

def b8950 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 51 70 262 249 249 249 249 249 505), lower := (rows 51 70 262 8 16 32 64 128 256), losses := [] }

theorem u8950 : Upper (D 1) (R 1) [50,68,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8950
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8951 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8951 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8951 : Upper (D 1) (R 1) [50,68,264] 13 := by
  apply FastRouting.sound _ _ [50,68,264] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r8951 c8951
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6489
  · exact u6490
  · exact u6491
  · exact u6492
  · exact u6493
  · exact u6494
  · exact u6495
  · exact u6496
  · exact u6497
  · exact u6498
  · exact u6499

def b8952 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 51 70 276 235 251 235 235 235 491), lower := (rows 51 70 276 8 16 32 64 128 256), losses := [] }

theorem u8952 : Upper (D 1) (R 1) [50,68,272] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8952
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8953 : PairBound 9 := { available := 187, camps := [{ cop := 2, region := 2, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 324 187 187 187 251 187 443), lower := (rows 51 70 324 8 16 32 64 128 256), losses := [] }

theorem u8953 : Upper (D 1) (R 1) [50,68,320] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8953
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8954 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8954 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8954 : Upper (D 1) (R 1) [50,68,384] 13 := by
  apply FastRouting.sound _ _ [50,68,384] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r8954 c8954
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6500
  · exact u6501
  · exact u6502
  · exact u6503
  · exact u6504
  · exact u6505
  · exact u6506
  · exact u6507
  · exact u6508
  · exact u6509
  · exact u6510

def b8955 : PairBound 9 := { available := 508, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 7 508 508 508 508 508 508), lower := (rows 51 194 7 8 16 32 64 128 256), losses := [] }

theorem u8955 : Upper (D 1) (R 1) [50,192,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8955
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8956 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8956 : Nat → Fin 9 := (fun _ => 0)

theorem u8956 : Upper (D 1) (R 1) [50,192,9] 13 := by
  apply FastRouting.sound _ _ [50,192,9] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192,258,260,272,320] r8956 c8956
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6517
  · exact u6518
  · exact u6519
  · exact u6520
  · exact u6521
  · exact u6522
  · exact u6523
  · exact u6524
  · exact u6525
  · exact u6526
  · exact u6527
  · exact u6528

theorem m8957_5 : Upper (D 1) (R 1) [50,192,10,5] 13 :=
  permutation_upper _ _ _ [50,192,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6517

def r8957 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8957 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | _ => 0)

theorem u8957 : Upper (D 1) (R 1) [50,192,10] 13 := by
  apply FastRouting.sound _ _ [50,192,10] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,192,257,260,272,320] r8957 c8957
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8957_5
  · exact u6529
  · exact u6530
  · exact u6531
  · exact u6532
  · exact u6533
  · exact u6534
  · exact u6535
  · exact u6536
  · exact u6537
  · exact u6538
  · exact u6539

def b8958 : PairBound 9 := { available := 494, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 21 494 510 494 494 494 494), lower := (rows 51 194 21 8 16 32 64 128 256), losses := [] }

theorem u8958 : Upper (D 1) (R 1) [50,192,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8958
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8959 : PairBound 9 := { available := 493, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 194 22 493 509 493 493 493 493), lower := (rows 51 194 22 8 16 32 64 128 256), losses := [] }

theorem u8959 : Upper (D 1) (R 1) [50,192,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8959
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8960_3 : Upper (D 1) (R 1) [50,192,24,3] 13 :=
  permutation_upper _ _ _ [50,192,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6511

theorem m8960_5 : Upper (D 1) (R 1) [50,192,24,5] 13 :=
  permutation_upper _ _ _ [50,192,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6519

theorem m8960_6 : Upper (D 1) (R 1) [50,192,24,6] 13 :=
  permutation_upper _ _ _ [50,192,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6530

theorem m8960_33 : Upper (D 1) (R 1) [50,192,24,33] 13 :=
  permutation_upper _ _ _ [50,192,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6540

theorem m8960_34 : Upper (D 1) (R 1) [50,192,24,34] 13 :=
  permutation_upper _ _ _ [50,192,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6547

def r8960 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 384 => (320,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8960 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 18 => 4 | 20 => 4 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | _ => 0)

theorem u8960 : Upper (D 1) (R 1) [50,192,24] 13 := by
  apply FastRouting.sound _ _ [50,192,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192,257,258,260,288,320] r8960 c8960
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8960_3
  · exact m8960_5
  · exact m8960_6
  · exact m8960_33
  · exact m8960_34
  · exact u6555
  · exact u6556
  · exact u6557
  · exact u6558
  · exact u6559
  · exact u6560
  · exact u6561
  · exact u6562
  · exact u6563
  · exact u6564
  · exact u6565

def b8961 : PairBound 9 := { available := 463, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 194 52 463 479 495 463 463 463), lower := (rows 51 194 52 8 16 32 64 128 256), losses := [] }

theorem u8961 : Upper (D 1) (R 1) [50,192,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8961
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8962_6 : Upper (D 1) (R 1) [50,192,65,6] 13 :=
  permutation_upper _ _ _ [50,192,10,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6532

theorem m8962_18 : Upper (D 1) (R 1) [50,192,65,18] 13 :=
  permutation_upper _ _ _ [50,192,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6548

theorem m8962_20 : Upper (D 1) (R 1) [50,192,65,20] 13 :=
  permutation_upper _ _ _ [50,192,24,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6556

theorem m8962_48 : Upper (D 1) (R 1) [50,192,65,48] 13 :=
  permutation_upper _ _ _ [50,192,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6566

def r8962 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8962 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8962 : Upper (D 1) (R 1) [50,192,65] 13 := by
  apply FastRouting.sound _ _ [50,192,65] 13 (by decide) (choices 2) [6,18,20,48,130,132,144,258,260,272,384] r8962 c8962
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8962_6
  · exact m8962_18
  · exact m8962_20
  · exact m8962_48
  · exact u6572
  · exact u6573
  · exact u6574
  · exact u6575
  · exact u6576
  · exact u6577
  · exact u6578

def b8963 : PairBound 9 := { available := 445, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 70 445 445 445 509 445 445), lower := (rows 51 194 70 8 16 32 64 128 256), losses := [] }

theorem u8963 : Upper (D 1) (R 1) [50,192,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8963
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8964_3 : Upper (D 1) (R 1) [50,192,72,3] 13 :=
  permutation_upper _ _ _ [50,192,3,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6512

theorem m8964_5 : Upper (D 1) (R 1) [50,192,72,5] 13 :=
  permutation_upper _ _ _ [50,192,9,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6522

theorem m8964_6 : Upper (D 1) (R 1) [50,192,72,6] 13 :=
  permutation_upper _ _ _ [50,192,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6533

theorem m8964_17 : Upper (D 1) (R 1) [50,192,72,17] 13 :=
  permutation_upper _ _ _ [50,192,17,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6541

theorem m8964_18 : Upper (D 1) (R 1) [50,192,72,18] 13 :=
  permutation_upper _ _ _ [50,192,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6549

theorem m8964_20 : Upper (D 1) (R 1) [50,192,72,20] 13 :=
  permutation_upper _ _ _ [50,192,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6558

theorem m8964_48 : Upper (D 1) (R 1) [50,192,72,48] 13 :=
  permutation_upper _ _ _ [50,192,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6567

theorem m8964_129 : Upper (D 1) (R 1) [50,192,72,129] 13 :=
  permutation_upper _ _ _ [50,192,65,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6573

theorem m8964_130 : Upper (D 1) (R 1) [50,192,72,130] 13 :=
  permutation_upper _ _ _ [50,192,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6579

def r8964 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 288 => (272,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8964 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 66 => 6 | 68 => 6 | 80 => 6 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8964 : Upper (D 1) (R 1) [50,192,72] 13 := by
  apply FastRouting.sound _ _ [50,192,72] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144,257,258,260,272,384] r8964 c8964
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8964_3
  · exact m8964_5
  · exact m8964_6
  · exact m8964_17
  · exact m8964_18
  · exact m8964_20
  · exact m8964_48
  · exact m8964_129
  · exact m8964_130
  · exact u6585
  · exact u6586
  · exact u6587
  · exact u6588
  · exact u6589
  · exact u6590
  · exact u6591

theorem m8965_3 : Upper (D 1) (R 1) [50,192,80,3] 13 :=
  permutation_upper _ _ _ [50,192,3,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6513

theorem m8965_5 : Upper (D 1) (R 1) [50,192,80,5] 13 :=
  permutation_upper _ _ _ [50,192,9,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6523

theorem m8965_6 : Upper (D 1) (R 1) [50,192,80,6] 13 :=
  permutation_upper _ _ _ [50,192,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6534

theorem m8965_33 : Upper (D 1) (R 1) [50,192,80,33] 13 :=
  permutation_upper _ _ _ [50,192,17,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6542

theorem m8965_34 : Upper (D 1) (R 1) [50,192,80,34] 13 :=
  permutation_upper _ _ _ [50,192,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6550

theorem m8965_36 : Upper (D 1) (R 1) [50,192,80,36] 13 :=
  permutation_upper _ _ _ [50,192,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6559

theorem m8965_129 : Upper (D 1) (R 1) [50,192,80,129] 13 :=
  permutation_upper _ _ _ [50,192,65,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6574

theorem m8965_130 : Upper (D 1) (R 1) [50,192,80,130] 13 :=
  permutation_upper _ _ _ [50,192,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6580

theorem m8965_132 : Upper (D 1) (R 1) [50,192,80,132] 13 :=
  permutation_upper _ _ _ [50,192,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6586

def r8965 : Route 9 := (fun mask => (mask,id))

def c8965 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 65 => 6 | 18 => 4 | 66 => 6 | 20 => 4 | 68 => 6 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 96 => 6 | 192 => 6 | 320 => 6 | _ => 0)

theorem u8965 : Upper (D 1) (R 1) [50,192,80] 13 := by
  apply FastRouting.sound _ _ [50,192,80] 13 (by decide) (choices 2) [3,5,6,33,34,36,129,130,132,160,257,258,260,288,384] r8965 c8965
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8965_3
  · exact m8965_5
  · exact m8965_6
  · exact m8965_33
  · exact m8965_34
  · exact m8965_36
  · exact m8965_129
  · exact m8965_130
  · exact m8965_132
  · exact u6592
  · exact u6593
  · exact u6594
  · exact u6595
  · exact u6596
  · exact u6597

def b8966 : PairBound 9 := { available := 319, camps := [{ cop := 1, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 194 196 319 319 319 383 447 319), lower := (rows 51 194 196 8 16 32 64 128 256), losses := [] }

theorem u8966 : Upper (D 1) (R 1) [50,192,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8966
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8967_6 : Upper (D 1) (R 1) [50,192,257,6] 13 :=
  permutation_upper _ _ _ [50,192,10,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6536

theorem m8967_18 : Upper (D 1) (R 1) [50,192,257,18] 13 :=
  permutation_upper _ _ _ [50,192,18,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6551

theorem m8967_20 : Upper (D 1) (R 1) [50,192,257,20] 13 :=
  permutation_upper _ _ _ [50,192,24,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6561

theorem m8967_48 : Upper (D 1) (R 1) [50,192,257,48] 13 :=
  permutation_upper _ _ _ [50,192,48,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6568

theorem m8967_66 : Upper (D 1) (R 1) [50,192,257,66] 13 :=
  permutation_upper _ _ _ [50,192,66,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6581

theorem m8967_68 : Upper (D 1) (R 1) [50,192,257,68] 13 :=
  permutation_upper _ _ _ [50,192,72,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6587

theorem m8967_80 : Upper (D 1) (R 1) [50,192,257,80] 13 :=
  permutation_upper _ _ _ [50,192,80,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6593

theorem m8967_192 : Upper (D 1) (R 1) [50,192,257,192] 13 :=
  permutation_upper _ _ _ [50,192,192,257] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6598

def r8967 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8967 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8967 : Upper (D 1) (R 1) [50,192,257] 13 := by
  apply FastRouting.sound _ _ [50,192,257] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192] r8967 c8967
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8967_6
  · exact m8967_18
  · exact m8967_20
  · exact m8967_48
  · exact m8967_66
  · exact m8967_68
  · exact m8967_80
  · exact m8967_192

theorem m8968_5 : Upper (D 1) (R 1) [50,192,258,5] 13 :=
  permutation_upper _ _ _ [50,192,9,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6525

theorem m8968_17 : Upper (D 1) (R 1) [50,192,258,17] 13 :=
  permutation_upper _ _ _ [50,192,17,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6543

theorem m8968_20 : Upper (D 1) (R 1) [50,192,258,20] 13 :=
  permutation_upper _ _ _ [50,192,24,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6562

theorem m8968_48 : Upper (D 1) (R 1) [50,192,258,48] 13 :=
  permutation_upper _ _ _ [50,192,48,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6569

theorem m8968_65 : Upper (D 1) (R 1) [50,192,258,65] 13 :=
  permutation_upper _ _ _ [50,192,65,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6575

theorem m8968_68 : Upper (D 1) (R 1) [50,192,258,68] 13 :=
  permutation_upper _ _ _ [50,192,72,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6588

theorem m8968_80 : Upper (D 1) (R 1) [50,192,258,80] 13 :=
  permutation_upper _ _ _ [50,192,80,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6594

theorem m8968_192 : Upper (D 1) (R 1) [50,192,258,192] 13 :=
  permutation_upper _ _ _ [50,192,192,258] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6599

def r8968 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8968 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8968 : Upper (D 1) (R 1) [50,192,258] 13 := by
  apply FastRouting.sound _ _ [50,192,258] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,192] r8968 c8968
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8968_5
  · exact m8968_17
  · exact m8968_20
  · exact m8968_48
  · exact m8968_65
  · exact m8968_68
  · exact m8968_80
  · exact m8968_192

theorem m8969_3 : Upper (D 1) (R 1) [50,192,264,3] 13 :=
  permutation_upper _ _ _ [50,192,3,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6514

theorem m8969_5 : Upper (D 1) (R 1) [50,192,264,5] 13 :=
  permutation_upper _ _ _ [50,192,9,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6526

theorem m8969_6 : Upper (D 1) (R 1) [50,192,264,6] 13 :=
  permutation_upper _ _ _ [50,192,10,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6537

theorem m8969_17 : Upper (D 1) (R 1) [50,192,264,17] 13 :=
  permutation_upper _ _ _ [50,192,17,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6544

theorem m8969_18 : Upper (D 1) (R 1) [50,192,264,18] 13 :=
  permutation_upper _ _ _ [50,192,18,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6552

theorem m8969_20 : Upper (D 1) (R 1) [50,192,264,20] 13 :=
  permutation_upper _ _ _ [50,192,24,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6563

theorem m8969_48 : Upper (D 1) (R 1) [50,192,264,48] 13 :=
  permutation_upper _ _ _ [50,192,48,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6570

theorem m8969_65 : Upper (D 1) (R 1) [50,192,264,65] 13 :=
  permutation_upper _ _ _ [50,192,65,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6576

theorem m8969_66 : Upper (D 1) (R 1) [50,192,264,66] 13 :=
  permutation_upper _ _ _ [50,192,66,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6582

theorem m8969_68 : Upper (D 1) (R 1) [50,192,264,68] 13 :=
  permutation_upper _ _ _ [50,192,72,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6589

theorem m8969_80 : Upper (D 1) (R 1) [50,192,264,80] 13 :=
  permutation_upper _ _ _ [50,192,80,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6595

theorem m8969_192 : Upper (D 1) (R 1) [50,192,264,192] 13 :=
  permutation_upper _ _ _ [50,192,192,260] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6600

def r8969 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8969 : Nat → Fin 9 := (fun mask => match mask with | 257 => 8 | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8969 : Upper (D 1) (R 1) [50,192,264] 13 := by
  apply FastRouting.sound _ _ [50,192,264] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,65,66,68,80,192] r8969 c8969
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8969_3
  · exact m8969_5
  · exact m8969_6
  · exact m8969_17
  · exact m8969_18
  · exact m8969_20
  · exact m8969_48
  · exact m8969_65
  · exact m8969_66
  · exact m8969_68
  · exact m8969_80
  · exact m8969_192

theorem m8970_3 : Upper (D 1) (R 1) [50,192,272,3] 13 :=
  permutation_upper _ _ _ [50,192,3,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6515

theorem m8970_5 : Upper (D 1) (R 1) [50,192,272,5] 13 :=
  permutation_upper _ _ _ [50,192,9,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6527

theorem m8970_6 : Upper (D 1) (R 1) [50,192,272,6] 13 :=
  permutation_upper _ _ _ [50,192,10,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6538

theorem m8970_33 : Upper (D 1) (R 1) [50,192,272,33] 13 :=
  permutation_upper _ _ _ [50,192,17,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6545

theorem m8970_34 : Upper (D 1) (R 1) [50,192,272,34] 13 :=
  permutation_upper _ _ _ [50,192,18,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6553

theorem m8970_36 : Upper (D 1) (R 1) [50,192,272,36] 13 :=
  permutation_upper _ _ _ [50,192,24,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6564

theorem m8970_65 : Upper (D 1) (R 1) [50,192,272,65] 13 :=
  permutation_upper _ _ _ [50,192,65,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6577

theorem m8970_66 : Upper (D 1) (R 1) [50,192,272,66] 13 :=
  permutation_upper _ _ _ [50,192,66,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6583

theorem m8970_68 : Upper (D 1) (R 1) [50,192,272,68] 13 :=
  permutation_upper _ _ _ [50,192,72,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6590

theorem m8970_96 : Upper (D 1) (R 1) [50,192,272,96] 13 :=
  permutation_upper _ _ _ [50,192,80,288] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6596

theorem m8970_192 : Upper (D 1) (R 1) [50,192,272,192] 13 :=
  permutation_upper _ _ _ [50,192,192,272] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6601

def r8970 : Route 9 := (fun mask => match mask with | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8970 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8970 : Upper (D 1) (R 1) [50,192,272] 13 := by
  apply FastRouting.sound _ _ [50,192,272] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,192] r8970 c8970
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8970_3
  · exact m8970_5
  · exact m8970_6
  · exact m8970_33
  · exact m8970_34
  · exact m8970_36
  · exact m8970_65
  · exact m8970_66
  · exact m8970_68
  · exact m8970_96
  · exact m8970_192

theorem m8971_3 : Upper (D 1) (R 1) [50,192,320,3] 13 :=
  permutation_upper _ _ _ [50,192,3,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6516

theorem m8971_5 : Upper (D 1) (R 1) [50,192,320,5] 13 :=
  permutation_upper _ _ _ [50,192,9,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6528

theorem m8971_6 : Upper (D 1) (R 1) [50,192,320,6] 13 :=
  permutation_upper _ _ _ [50,192,10,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6539

theorem m8971_17 : Upper (D 1) (R 1) [50,192,320,17] 13 :=
  permutation_upper _ _ _ [50,192,17,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6546

theorem m8971_18 : Upper (D 1) (R 1) [50,192,320,18] 13 :=
  permutation_upper _ _ _ [50,192,18,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6554

theorem m8971_20 : Upper (D 1) (R 1) [50,192,320,20] 13 :=
  permutation_upper _ _ _ [50,192,24,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6565

theorem m8971_48 : Upper (D 1) (R 1) [50,192,320,48] 13 :=
  permutation_upper _ _ _ [50,192,48,320] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6571

theorem m8971_129 : Upper (D 1) (R 1) [50,192,320,129] 13 :=
  permutation_upper _ _ _ [50,192,65,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6578

theorem m8971_130 : Upper (D 1) (R 1) [50,192,320,130] 13 :=
  permutation_upper _ _ _ [50,192,66,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6584

theorem m8971_132 : Upper (D 1) (R 1) [50,192,320,132] 13 :=
  permutation_upper _ _ _ [50,192,72,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6591

theorem m8971_144 : Upper (D 1) (R 1) [50,192,320,144] 13 :=
  permutation_upper _ _ _ [50,192,80,384] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6597

def r8971 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8971 : Nat → Fin 9 := (fun mask => match mask with | 65 => 6 | 257 => 8 | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u8971 : Upper (D 1) (R 1) [50,192,320] 13 := by
  apply FastRouting.sound _ _ [50,192,320] 13 (by decide) (choices 2) [3,5,6,17,18,20,48,129,130,132,144] r8971 c8971
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8971_3
  · exact m8971_5
  · exact m8971_6
  · exact m8971_17
  · exact m8971_18
  · exact m8971_20
  · exact m8971_48
  · exact m8971_129
  · exact m8971_130
  · exact m8971_132
  · exact m8971_144

def b8972 : PairBound 9 := { available := 244, camps := [{ cop := 2, region := 248, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 14 252 244 244 244 244 500), lower := (rows 51 259 14 8 16 32 64 128 256), losses := [] }

theorem u8972 : Upper (D 1) (R 1) [50,257,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8972
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8973 : PairBound 9 := { available := 236, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 259 22 236 252 236 236 236 492), lower := (rows 51 259 22 8 16 32 64 128 256), losses := [] }

theorem u8973 : Upper (D 1) (R 1) [50,257,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8973
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8974_6 : Upper (D 1) (R 1) [50,257,24,6] 13 :=
  permutation_upper _ _ _ [50,257,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6602

theorem m8974_34 : Upper (D 1) (R 1) [50,257,24,34] 13 :=
  permutation_upper _ _ _ [50,257,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6606

def r8974 : Route 9 := (fun mask => match mask with | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 160 => (96,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8974 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8974 : Upper (D 1) (R 1) [50,257,24] 13 := by
  apply FastRouting.sound _ _ [50,257,24] 13 (by decide) (choices 2) [6,34,36,66,68,96,192] r8974 c8974
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8974_6
  · exact m8974_34
  · exact u6610
  · exact u6611
  · exact u6612
  · exact u6613
  · exact u6614

def b8975 : PairBound 9 := { available := 206, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 259 52 206 222 238 206 206 462), lower := (rows 51 259 52 8 16 32 64 128 256), losses := [] }

theorem u8975 : Upper (D 1) (R 1) [50,257,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8975
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8976 : PairBound 9 := { available := 252, camps := [{ cop := 2, region := 184, targets := 2 }], pairs := [(3,1)], upper := (rows 51 259 70 252 252 252 252 252 508), lower := (rows 51 259 70 8 16 32 64 128 256), losses := [] }

theorem u8976 : Upper (D 1) (R 1) [50,257,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8976
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8977_6 : Upper (D 1) (R 1) [50,257,72,6] 13 :=
  permutation_upper _ _ _ [50,257,10,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6603

theorem m8977_18 : Upper (D 1) (R 1) [50,257,72,18] 13 :=
  permutation_upper _ _ _ [50,257,18,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6607

theorem m8977_20 : Upper (D 1) (R 1) [50,257,72,20] 13 :=
  permutation_upper _ _ _ [50,257,24,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6612

theorem m8977_48 : Upper (D 1) (R 1) [50,257,72,48] 13 :=
  permutation_upper _ _ _ [50,257,48,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6615

theorem m8977_66 : Upper (D 1) (R 1) [50,257,72,66] 13 :=
  permutation_upper _ _ _ [50,257,66,68] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6617

theorem m8977_130 : Upper (D 1) (R 1) [50,257,72,130] 13 :=
  permutation_upper _ _ _ [50,257,66,132] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6619

def r8977 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8977 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8977 : Upper (D 1) (R 1) [50,257,72] 13 := by
  apply FastRouting.sound _ _ [50,257,72] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r8977 c8977
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8977_6
  · exact m8977_18
  · exact m8977_20
  · exact m8977_48
  · exact m8977_66
  · exact u6622
  · exact u6623
  · exact m8977_130
  · exact u6624
  · exact u6625
  · exact u6626

theorem m8978_6 : Upper (D 1) (R 1) [50,257,80,6] 13 :=
  permutation_upper _ _ _ [50,257,10,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6604

theorem m8978_34 : Upper (D 1) (R 1) [50,257,80,34] 13 :=
  permutation_upper _ _ _ [50,257,18,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6608

theorem m8978_36 : Upper (D 1) (R 1) [50,257,80,36] 13 :=
  permutation_upper _ _ _ [50,257,24,96] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6613

theorem m8978_66 : Upper (D 1) (R 1) [50,257,80,66] 13 :=
  permutation_upper _ _ _ [50,257,66,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6618

theorem m8978_68 : Upper (D 1) (R 1) [50,257,80,68] 13 :=
  permutation_upper _ _ _ [50,257,72,80] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6623

theorem m8978_130 : Upper (D 1) (R 1) [50,257,80,130] 13 :=
  permutation_upper _ _ _ [50,257,66,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6620

theorem m8978_132 : Upper (D 1) (R 1) [50,257,80,132] 13 :=
  permutation_upper _ _ _ [50,257,72,144] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6625

def r8978 : Route 9 := (fun mask => (mask,id))

def c8978 : Nat → Fin 9 := (fun mask => match mask with | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8978 : Upper (D 1) (R 1) [50,257,80] 13 := by
  apply FastRouting.sound _ _ [50,257,80] 13 (by decide) (choices 2) [6,34,36,66,68,96,130,132,160,192] r8978 c8978
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8978_6
  · exact m8978_34
  · exact m8978_36
  · exact m8978_66
  · exact m8978_68
  · exact u6627
  · exact m8978_130
  · exact m8978_132
  · exact u6628
  · exact u6629

theorem m8979_6 : Upper (D 1) (R 1) [50,257,192,6] 13 :=
  permutation_upper _ _ _ [50,257,10,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6605

theorem m8979_18 : Upper (D 1) (R 1) [50,257,192,18] 13 :=
  permutation_upper _ _ _ [50,257,18,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6609

theorem m8979_20 : Upper (D 1) (R 1) [50,257,192,20] 13 :=
  permutation_upper _ _ _ [50,257,24,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6614

theorem m8979_48 : Upper (D 1) (R 1) [50,257,192,48] 13 :=
  permutation_upper _ _ _ [50,257,48,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6616

theorem m8979_66 : Upper (D 1) (R 1) [50,257,192,66] 13 :=
  permutation_upper _ _ _ [50,257,66,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6621

theorem m8979_68 : Upper (D 1) (R 1) [50,257,192,68] 13 :=
  permutation_upper _ _ _ [50,257,72,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6626

theorem m8979_80 : Upper (D 1) (R 1) [50,257,192,80] 13 :=
  permutation_upper _ _ _ [50,257,80,192] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6629

def r8979 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 132 => (68,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8979 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8979 : Upper (D 1) (R 1) [50,257,192] 13 := by
  apply FastRouting.sound _ _ [50,257,192] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,192] r8979 c8979
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8979_6
  · exact m8979_18
  · exact m8979_20
  · exact m8979_48
  · exact m8979_66
  · exact m8979_68
  · exact m8979_80
  · exact u6630

def b8980 : PairBound 9 := { available := 248, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 262 7 248 248 248 248 248 504), lower := (rows 51 262 7 8 16 32 64 128 256), losses := [] }

theorem u8980 : Upper (D 1) (R 1) [50,260,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8980
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8981 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8981 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8981 : Upper (D 1) (R 1) [50,260,9] 13 := by
  apply FastRouting.sound _ _ [50,260,9] 13 (by decide) (choices 2) [18,48,66,80,192] r8981 c8981
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  · exact u6631
  · exact u6632
  · exact u6633
  · exact u6634
  · exact u6635

def b8982 : PairBound 9 := { available := 241, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 14 249 241 241 241 241 497), lower := (rows 51 262 14 8 16 32 64 128 256), losses := [] }

theorem u8982 : Upper (D 1) (R 1) [50,260,10] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8982
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8983 : PairBound 9 := { available := 234, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 21 234 250 234 234 234 490), lower := (rows 51 262 21 8 16 32 64 128 256), losses := [] }

theorem u8983 : Upper (D 1) (R 1) [50,260,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8983
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8984 : PairBound 9 := { available := 233, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 262 22 233 249 233 233 233 489), lower := (rows 51 262 22 8 16 32 64 128 256), losses := [] }

theorem u8984 : Upper (D 1) (R 1) [50,260,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8984
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8985 : PairBound 9 := { available := 227, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 51 262 28 235 243 227 227 227 483), lower := (rows 51 262 28 8 16 32 64 128 256), losses := [] }

theorem u8985 : Upper (D 1) (R 1) [50,260,24] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8985
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8986 : PairBound 9 := { available := 203, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 262 52 203 219 235 203 203 459), lower := (rows 51 262 52 8 16 32 64 128 256), losses := [] }

theorem u8986 : Upper (D 1) (R 1) [50,260,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8986
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8987 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8987 : Nat → Fin 9 := (fun mask => match mask with | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8987 : Upper (D 1) (R 1) [50,260,65] 13 := by
  apply FastRouting.sound _ _ [50,260,65] 13 (by decide) (choices 2) [18,48,66,80,130,144,192] r8987 c8987
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6636
  · exact u6637
  · exact u6638
  · exact u6639
  · exact u6640
  · exact u6641
  · exact u6642

def b8988 : PairBound 9 := { available := 249, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 51 262 70 249 249 249 249 249 505), lower := (rows 51 262 70 8 16 32 64 128 256), losses := [] }

theorem u8988 : Upper (D 1) (R 1) [50,260,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8988
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8989 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8989 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8989 : Upper (D 1) (R 1) [50,260,72] 13 := by
  apply FastRouting.sound _ _ [50,260,72] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,129,130,144,192] r8989 c8989
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6643
  · exact u6644
  · exact u6645
  · exact u6646
  · exact u6647
  · exact u6648
  · exact u6649
  · exact u6650
  · exact u6651
  · exact u6652
  · exact u6653

def b8990 : PairBound 9 := { available := 235, camps := [{ cop := 0, region := 200, targets := 16 }], pairs := [(3,4)], upper := (rows 51 262 84 235 251 235 235 235 491), lower := (rows 51 262 84 8 16 32 64 128 256), losses := [] }

theorem u8990 : Upper (D 1) (R 1) [50,260,80] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8990
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8991 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 129 => (65,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 130 => (66,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 144 => (80,(fun i => match i.val with | 6 => 7 | 7 => 6 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | 6 => 7 | 7 => 6 | _ => i)) | _ => (mask,id))

def c8991 : Nat → Fin 9 := (fun mask => match mask with | 5 => 2 | 257 => 8 | 6 => 2 | 258 => 8 | 20 => 2 | 36 => 2 | 68 => 2 | 132 => 2 | 260 => 2 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8991 : Upper (D 1) (R 1) [50,260,192] 13 := by
  apply FastRouting.sound _ _ [50,260,192] 13 (by decide) (choices 2) [3,17,18,48,65,66,80,192] r8991 c8991
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6654
  · exact u6655
  · exact u6656
  · exact u6657
  · exact u6658
  · exact u6659
  · exact u6660
  · exact u6661

def b8992 : PairBound 9 := { available := 252, camps := [{ cop := 0, region := 4, targets := 16 }], pairs := [(2,4)], upper := (rows 51 322 7 252 252 252 252 252 508), lower := (rows 51 322 7 8 16 32 64 128 256), losses := [] }

theorem u8992 : Upper (D 1) (R 1) [50,320,3] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8992
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r8993 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8993 : Nat → Fin 9 := (fun mask => match mask with | 258 => 8 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8993 : Upper (D 1) (R 1) [50,320,9] 13 := by
  apply FastRouting.sound _ _ [50,320,9] 13 (by decide) (choices 2) [6,18,20,48,66,68,80,130,132,144,192] r8993 c8993
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact u6668
  · exact u6669
  · exact u6670
  · exact u6671
  · exact u6672
  · exact u6673
  · exact u6674
  · exact u6675
  · exact u6676
  · exact u6677
  · exact u6678

theorem m8994_5 : Upper (D 1) (R 1) [50,320,10,5] 13 :=
  permutation_upper _ _ _ [50,320,9,6] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6668

def r8994 : Route 9 := (fun mask => match mask with | 33 => (17,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 96 => (80,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8994 : Nat → Fin 9 := (fun mask => match mask with | 3 => 1 | 257 => 8 | 6 => 1 | 18 => 1 | 34 => 1 | 66 => 1 | 130 => 1 | 258 => 1 | 260 => 8 | 272 => 8 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8994 : Upper (D 1) (R 1) [50,320,10] 13 := by
  apply FastRouting.sound _ _ [50,320,10] 13 (by decide) (choices 2) [5,17,20,48,65,68,80,129,132,144,192] r8994 c8994
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8994_5
  · exact u6679
  · exact u6680
  · exact u6681
  · exact u6682
  · exact u6683
  · exact u6684
  · exact u6685
  · exact u6686
  · exact u6687
  · exact u6688

def b8995 : PairBound 9 := { available := 238, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 21 238 254 238 238 238 494), lower := (rows 51 322 21 8 16 32 64 128 256), losses := [] }

theorem u8995 : Upper (D 1) (R 1) [50,320,17] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8995
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b8996 : PairBound 9 := { available := 237, camps := [{ cop := 0, region := 4, targets := 32 }], pairs := [(2,5)], upper := (rows 51 322 22 237 253 237 237 237 493), lower := (rows 51 322 22 8 16 32 64 128 256), losses := [] }

theorem u8996 : Upper (D 1) (R 1) [50,320,18] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8996
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8997_3 : Upper (D 1) (R 1) [50,320,24,3] 13 :=
  permutation_upper _ _ _ [50,320,3,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6662

theorem m8997_5 : Upper (D 1) (R 1) [50,320,24,5] 13 :=
  permutation_upper _ _ _ [50,320,9,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6670

theorem m8997_6 : Upper (D 1) (R 1) [50,320,24,6] 13 :=
  permutation_upper _ _ _ [50,320,10,20] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6680

theorem m8997_33 : Upper (D 1) (R 1) [50,320,24,33] 13 :=
  permutation_upper _ _ _ [50,320,17,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6689

theorem m8997_34 : Upper (D 1) (R 1) [50,320,24,34] 13 :=
  permutation_upper _ _ _ [50,320,18,36] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6696

def r8997 : Route 9 := (fun mask => (mask,id))

def c8997 : Nat → Fin 9 := (fun mask => match mask with | 17 => 4 | 257 => 8 | 18 => 4 | 258 => 8 | 20 => 4 | 260 => 8 | 48 => 4 | 80 => 4 | 144 => 4 | 272 => 4 | 288 => 8 | 320 => 8 | 384 => 8 | _ => 0)

theorem u8997 : Upper (D 1) (R 1) [50,320,24] 13 := by
  apply FastRouting.sound _ _ [50,320,24] 13 (by decide) (choices 2) [3,5,6,33,34,36,65,66,68,96,129,130,132,160,192] r8997 c8997
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8997_3
  · exact m8997_5
  · exact m8997_6
  · exact m8997_33
  · exact m8997_34
  · exact u6704
  · exact u6705
  · exact u6706
  · exact u6707
  · exact u6708
  · exact u6709
  · exact u6710
  · exact u6711
  · exact u6712
  · exact u6713

def b8998 : PairBound 9 := { available := 207, camps := [{ cop := 0, region := 4, targets := 2 }], pairs := [(2,1)], upper := (rows 51 322 52 207 223 239 207 207 463), lower := (rows 51 322 52 8 16 32 64 128 256), losses := [] }

theorem u8998 : Upper (D 1) (R 1) [50,320,48] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b8998
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m8999_6 : Upper (D 1) (R 1) [50,320,65,6] 13 :=
  permutation_upper _ _ _ [50,320,10,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6682

theorem m8999_18 : Upper (D 1) (R 1) [50,320,65,18] 13 :=
  permutation_upper _ _ _ [50,320,18,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6697

theorem m8999_20 : Upper (D 1) (R 1) [50,320,65,20] 13 :=
  permutation_upper _ _ _ [50,320,24,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6705

theorem m8999_48 : Upper (D 1) (R 1) [50,320,65,48] 13 :=
  permutation_upper _ _ _ [50,320,48,65] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 2 | 4 => 4 | 5 => 5 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u6714

def r8999 : Route 9 := (fun mask => match mask with | 34 => (18,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 36 => (20,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | 160 => (144,(fun i => match i.val with | 4 => 5 | 5 => 4 | _ => i)) | _ => (mask,id))

def c8999 : Nat → Fin 9 := (fun mask => match mask with | 66 => 6 | 258 => 8 | 68 => 6 | 260 => 8 | 80 => 6 | 272 => 8 | 96 => 6 | 288 => 8 | 192 => 6 | 320 => 6 | 384 => 8 | _ => 0)

theorem u8999 : Upper (D 1) (R 1) [50,320,65] 13 := by
  apply FastRouting.sound _ _ [50,320,65] 13 (by decide) (choices 2) [6,18,20,48,130,132,144] r8999 c8999
    (by exact cover_two)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact m8999_6
  · exact m8999_18
  · exact m8999_20
  · exact m8999_48
  · exact u6720
  · exact u6721
  · exact u6722

#print axioms u8999
end Delivery.IrregularNine14.P01
