import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0020
import IrregularNine14P01C0021

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4500 : PairBound 9 := { available := 75, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 44 144 107 75 203 331), lower := (rows 113 386 22 44 144 32 64 128 256), losses := [] }

theorem u4500 : Upper (D 1) (R 1) [112,384,18,36,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4500
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4501 : PairBound 9 := { available := 108, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 137 18 108 108 236 364), lower := (rows 113 386 22 137 18 32 64 128 256), losses := [] }

theorem u4501 : Upper (D 1) (R 1) [112,384,18,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4501
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4502 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 386 22 137 20 106 106 234 362), lower := (rows 113 386 22 137 20 32 64 128 256), losses := [] }

theorem u4502 : Upper (D 1) (R 1) [112,384,18,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4502
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4503 : PairBound 9 := { available := 102, camps := [], pairs := [], upper := (rows 113 386 22 137 24 102 102 230 358), lower := (rows 113 386 22 137 24 32 64 128 256), losses := [] }

theorem u4503 : Upper (D 1) (R 1) [112,384,18,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4503
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4504 : PairBound 9 := { available := 78, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 22 137 48 110 78 206 334), lower := (rows 113 386 22 137 48 32 64 128 256), losses := [] }

theorem u4504 : Upper (D 1) (R 1) [112,384,18,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4504
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4505 : PairBound 9 := { available := 106, camps := [], pairs := [], upper := (rows 113 386 22 140 17 106 106 234 362), lower := (rows 113 386 22 140 17 32 64 128 256), losses := [] }

theorem u4505 : Upper (D 1) (R 1) [112,384,18,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4505
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4506 : PairBound 9 := { available := 105, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 140 18 105 105 233 361), lower := (rows 113 386 22 140 18 32 64 128 256), losses := [] }

theorem u4506 : Upper (D 1) (R 1) [112,384,18,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4506
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4507 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 386 22 140 24 99 99 227 355), lower := (rows 113 386 22 140 24 32 64 128 256), losses := [] }

theorem u4507 : Upper (D 1) (R 1) [112,384,18,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4507
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4508 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 386 22 140 48 107 75 203 331), lower := (rows 113 386 22 140 48 32 64 128 256), losses := [] }

theorem u4508 : Upper (D 1) (R 1) [112,384,18,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4508
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4509 : PairBound 9 := { available := 78, camps := [], pairs := [], upper := (rows 113 386 22 168 17 110 78 206 334), lower := (rows 113 386 22 168 17 32 64 128 256), losses := [] }

theorem u4509 : Upper (D 1) (R 1) [112,384,18,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4509
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4510 : PairBound 9 := { available := 77, camps := [{ cop := 1, region := 20, targets := 32 }], pairs := [(2,5)], upper := (rows 113 386 22 168 18 109 77 205 333), lower := (rows 113 386 22 168 18 32 64 128 256), losses := [] }

theorem u4510 : Upper (D 1) (R 1) [112,384,18,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4510
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4511 : PairBound 9 := { available := 75, camps := [], pairs := [], upper := (rows 113 386 22 168 20 107 75 203 331), lower := (rows 113 386 22 168 20 32 64 128 256), losses := [] }

theorem u4511 : Upper (D 1) (R 1) [112,384,18,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4511
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4512 : PairBound 9 := { available := 71, camps := [], pairs := [], upper := (rows 113 386 22 168 24 103 71 199 327), lower := (rows 113 386 22 168 24 32 64 128 256), losses := [] }

theorem u4512 : Upper (D 1) (R 1) [112,384,18,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4512
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4513 : PairBound 9 := { available := 15, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 22 168 80 47 79 143 271), lower := (rows 113 386 22 168 80 32 64 128 256), losses := [] }

theorem u4513 : Upper (D 1) (R 1) [112,384,18,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4513
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4514 : PairBound 9 := { available := 70, camps := [], pairs := [], upper := (rows 113 386 28 168 17 102 70 198 326), lower := (rows 113 386 28 168 17 32 64 128 256), losses := [] }

theorem u4514 : Upper (D 1) (R 1) [112,384,24,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4514
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4515 : Route 9 := (fun mask => (mask,id))

def c4515 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4515 : Upper (D 1) (R 1) [112,384,24,160,2] 13 := by
  apply FastRouting.sound _ _ [112,384,24,160,2] 13 (by decide) (choices 1) [1,2,4,64] r4515 c4515
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1253
  · exact u1254
  · exact u1255
  · exact u1256

def b4516 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 113 386 28 168 20 99 67 195 323), lower := (rows 113 386 28 168 20 32 64 128 256), losses := [] }

theorem u4516 : Upper (D 1) (R 1) [112,384,24,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4516
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4517 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 386 28 168 80 39 71 135 263), lower := (rows 113 386 28 168 80 32 64 128 256), losses := [] }

theorem u4517 : Upper (D 1) (R 1) [112,384,24,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4517
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4518 : PairBound 9 := { available := 224, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 88 18 224 224 224 480), lower := (rows 263 11 52 88 18 32 64 128 256), losses := [] }

theorem u4518 : Upper (D 1) (R 1) [262,9,48,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4518
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4519 : PairBound 9 := { available := 194, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 88 48 226 194 194 450), lower := (rows 263 11 52 88 48 32 64 128 256), losses := [] }

theorem u4519 : Upper (D 1) (R 1) [262,9,48,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4519
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4520 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 263 11 52 88 80 162 226 162 418), lower := (rows 263 11 52 88 80 32 64 128 256), losses := [] }

theorem u4520 : Upper (D 1) (R 1) [262,9,48,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4520
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4521 : Route 9 := (fun mask => (mask,id))

def c4521 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4521 : Upper (D 1) (R 1) [262,9,48,80,128] 13 := by
  apply FastRouting.sound _ _ [262,9,48,80,128] 13 (by decide) (choices 1) [2,64,128] r4521 c4521
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1257
  · exact u1258
  · exact u1259

def b4522 : PairBound 9 := { available := 240, camps := [{ cop := 4, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 263 11 52 200 18 240 240 240 496), lower := (rows 263 11 52 200 18 32 64 128 256), losses := [] }

theorem u4522 : Upper (D 1) (R 1) [262,9,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4522
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4523 : PairBound 9 := { available := 210, camps := [{ cop := 2, region := 459, targets := 32 }], pairs := [(0,5)], upper := (rows 263 11 52 200 48 242 210 210 466), lower := (rows 263 11 52 200 48 32 64 128 256), losses := [] }

theorem u4523 : Upper (D 1) (R 1) [262,9,48,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4523
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4524_2 : Upper (D 1) (R 1) [262,9,48,192,64,2] 13 :=
  permutation_upper _ _ _ [262,9,48,192,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1260

theorem m4524_16 : Upper (D 1) (R 1) [262,9,48,192,64,16] 13 :=
  permutation_upper _ _ _ [262,9,48,192,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1261

def r4524 : Route 9 := (fun mask => (mask,id))

def c4524 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4524 : Upper (D 1) (R 1) [262,9,48,192,64] 13 := by
  apply FastRouting.sound _ _ [262,9,48,192,64] 13 (by decide) (choices 1) [2,16,128] r4524 c4524
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4524_2
  · exact m4524_16
  · exact u1262

def b4525 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 44 88 18 224 224 224 480), lower := (rows 263 19 44 88 18 32 64 128 256), losses := [] }

theorem u4525 : Upper (D 1) (R 1) [262,17,40,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4525
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4526 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 88 48 226 194 194 450), lower := (rows 263 19 44 88 48 32 64 128 256), losses := [] }

theorem u4526 : Upper (D 1) (R 1) [262,17,40,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4526
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4527 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 263 19 44 88 80 162 226 162 418), lower := (rows 263 19 44 88 80 32 64 128 256), losses := [] }

theorem u4527 : Upper (D 1) (R 1) [262,17,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4527
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4528 : Route 9 := (fun mask => (mask,id))

def c4528 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4528 : Upper (D 1) (R 1) [262,17,40,80,128] 13 := by
  apply FastRouting.sound _ _ [262,17,40,80,128] 13 (by decide) (choices 1) [2,64,128] r4528 c4528
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1263
  · exact u1264
  · exact u1265

def b4529 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 44 200 18 240 240 240 496), lower := (rows 263 19 44 200 18 32 64 128 256), losses := [] }

theorem u4529 : Upper (D 1) (R 1) [262,17,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4529
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4530 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 44 200 48 242 210 210 466), lower := (rows 263 19 44 200 48 32 64 128 256), losses := [] }

theorem u4530 : Upper (D 1) (R 1) [262,17,40,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4530
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4531 : Route 9 := (fun mask => (mask,id))

def c4531 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4531 : Upper (D 1) (R 1) [262,17,40,192,64] 13 := by
  apply FastRouting.sound _ _ [262,17,40,192,64] 13 (by decide) (choices 1) [2,16,128] r4531 c4531
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1266
  · exact u1267
  · exact u1268

def b4532 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 56 18 232 200 200 456), lower := (rows 263 19 100 56 18 32 64 128 256), losses := [] }

theorem u4532 : Upper (D 1) (R 1) [262,17,96,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4532
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4533 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 263 19 100 56 24 226 194 194 450), lower := (rows 263 19 100 56 24 32 64 128 256), losses := [] }

theorem u4533 : Upper (D 1) (R 1) [262,17,96,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4533
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4534 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 263 19 100 56 80 170 202 138 394), lower := (rows 263 19 100 56 80 32 64 128 256), losses := [] }

theorem u4534 : Upper (D 1) (R 1) [262,17,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4534
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4535 : Route 9 := (fun mask => (mask,id))

def c4535 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4535 : Upper (D 1) (R 1) [262,17,96,48,128] 13 := by
  apply FastRouting.sound _ _ [262,17,96,48,128] 13 (by decide) (choices 1) [2,8,64,128] r4535 c4535
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1269
  · exact u1270
  · exact u1271
  · exact u1272

def b4536 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 152 18 232 232 232 488), lower := (rows 263 19 100 152 18 32 64 128 256), losses := [] }

theorem u4536 : Upper (D 1) (R 1) [262,17,96,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4536
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4537 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 263 19 100 152 24 226 226 226 482), lower := (rows 263 19 100 152 24 32 64 128 256), losses := [] }

theorem u4537 : Upper (D 1) (R 1) [262,17,96,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4537
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4538 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 263 19 100 152 48 234 202 202 458), lower := (rows 263 19 100 152 48 32 64 128 256), losses := [] }

theorem u4538 : Upper (D 1) (R 1) [262,17,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4538
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4539 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 263 19 100 152 144 106 106 234 362), lower := (rows 263 19 100 152 144 32 64 128 256), losses := [] }

theorem u4539 : Upper (D 1) (R 1) [262,17,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4539
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4540 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 19 100 168 18 248 216 216 472), lower := (rows 263 19 100 168 18 32 64 128 256), losses := [] }

theorem u4540 : Upper (D 1) (R 1) [262,17,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4541 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 263 19 100 168 24 242 210 210 466), lower := (rows 263 19 100 168 24 32 64 128 256), losses := [] }

theorem u4541 : Upper (D 1) (R 1) [262,17,96,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4541
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4542 : PairBound 9 := { available := 154, camps := [{ cop := 1, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 263 19 100 168 80 186 218 154 410), lower := (rows 263 19 100 168 80 32 64 128 256), losses := [] }

theorem u4542 : Upper (D 1) (R 1) [262,17,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4542
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4543 : Route 9 := (fun mask => (mask,id))

def c4543 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4543 : Upper (D 1) (R 1) [262,17,96,160,128] 13 := by
  apply FastRouting.sound _ _ [262,17,96,160,128] 13 (by decide) (choices 1) [2,8,16,64] r4543 c4543
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1273
  · exact u1274
  · exact u1275
  · exact u1276

def b4544 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 37 200 18 240 240 240 496), lower := (rows 263 26 37 200 18 32 64 128 256), losses := [] }

theorem u4544 : Upper (D 1) (R 1) [262,24,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4545 : PairBound 9 := { available := 210, camps := [{ cop := 4, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 37 200 48 242 210 210 466), lower := (rows 263 26 37 200 48 32 64 128 256), losses := [] }

theorem u4545 : Upper (D 1) (R 1) [262,24,33,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4546 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6)], upper := (rows 263 26 37 200 80 178 242 178 434), lower := (rows 263 26 37 200 80 32 64 128 256), losses := [] }

theorem u4546 : Upper (D 1) (R 1) [262,24,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4547 : PairBound 9 := { available := 240, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 137 18 240 240 240 496), lower := (rows 263 26 100 137 18 32 64 128 256), losses := [] }

theorem u4547 : Upper (D 1) (R 1) [262,24,96,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4547
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4548 : PairBound 9 := { available := 210, camps := [], pairs := [(3,5)], upper := (rows 263 26 100 137 48 242 210 210 466), lower := (rows 263 26 100 137 48 32 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 9 16 0 66 130 258), good := (rows 463 474 68 137 16 0 64 128 256) }] }

theorem u4548 : Upper (D 1) (R 1) [262,24,96,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4548
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4549 : PairBound 9 := { available := 114, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 263 26 100 137 144 114 114 242 370), lower := (rows 263 26 100 137 144 32 64 128 256), losses := [] }

theorem u4549 : Upper (D 1) (R 1) [262,24,96,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4550 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 263 26 100 168 17 242 210 210 466), lower := (rows 263 26 100 168 17 32 64 128 256), losses := [] }

theorem u4550 : Upper (D 1) (R 1) [262,24,96,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4551 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 263 26 100 168 18 241 209 209 465), lower := (rows 263 26 100 168 18 32 64 128 256), losses := [] }

theorem u4551 : Upper (D 1) (R 1) [262,24,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4551
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4552 : Route 9 := (fun mask => (mask,id))

def c4552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4552 : Upper (D 1) (R 1) [262,24,96,160,64] 13 := by
  apply FastRouting.sound _ _ [262,24,96,160,64] 13 (by decide) (choices 1) [1,2,16,128] r4552 c4552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1277
  · exact u1278
  · exact u1279
  · exact u1280

def b4553 : PairBound 9 := { available := 83, camps := [{ cop := 1, region := 357, targets := 128 }], pairs := [(0,7)], upper := (rows 263 26 100 168 144 115 83 211 339), lower := (rows 263 26 100 168 144 32 64 128 256), losses := [] }

theorem u4553 : Upper (D 1) (R 1) [262,24,96,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4553
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4554 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 13 74 48 240 208 208 464), lower := (rows 263 50 13 74 48 32 64 128 256), losses := [] }

theorem u4554 : Upper (D 1) (R 1) [262,48,9,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4554
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4555 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 74 80 176 240 176 432), lower := (rows 263 50 13 74 80 32 64 128 256), losses := [] }

theorem u4555 : Upper (D 1) (R 1) [262,48,9,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4555
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4556_16 : Upper (D 1) (R 1) [262,48,9,66,128,16] 13 :=
  permutation_upper _ _ _ [262,48,9,66,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1281

theorem m4556_64 : Upper (D 1) (R 1) [262,48,9,66,128,64] 13 :=
  permutation_upper _ _ _ [262,48,9,66,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1282

def r4556 : Route 9 := (fun mask => (mask,id))

def c4556 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4556 : Upper (D 1) (R 1) [262,48,9,66,128] 13 := by
  apply FastRouting.sound _ _ [262,48,9,66,128] 13 (by decide) (choices 1) [16,64,128] r4556 c4556
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4556_16
  · exact m4556_64
  · exact u1283

def b4557 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 88 18 224 224 224 480), lower := (rows 263 50 13 88 18 32 64 128 256), losses := [] }

theorem u4557 : Upper (D 1) (R 1) [262,48,9,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4557
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4558 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 13 88 48 226 194 194 450), lower := (rows 263 50 13 88 48 32 64 128 256), losses := [] }

theorem u4558 : Upper (D 1) (R 1) [262,48,9,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4558
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4559 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 263 50 13 88 80 162 226 162 418), lower := (rows 263 50 13 88 80 32 64 128 256), losses := [] }

theorem u4559 : Upper (D 1) (R 1) [262,48,9,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4559
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4559
end Delivery.IrregularNine14.P01
