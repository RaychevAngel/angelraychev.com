import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0021

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r4560 : Route 9 := (fun mask => (mask,id))

def c4560 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4560 : Upper (D 1) (R 1) [262,48,9,80,128] 13 := by
  apply FastRouting.sound _ _ [262,48,9,80,128] 13 (by decide) (choices 1) [2,64,128] r4560 c4560
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1284
  · exact u1285
  · exact u1286

def b4561 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 200 18 240 240 240 496), lower := (rows 263 50 13 200 18 32 64 128 256), losses := [] }

theorem u4561 : Upper (D 1) (R 1) [262,48,9,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 13 200 48 242 210 210 466), lower := (rows 263 50 13 200 48 32 64 128 256), losses := [] }

theorem u4562 : Upper (D 1) (R 1) [262,48,9,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 13 200 80 178 242 178 434), lower := (rows 263 50 13 200 80 32 64 128 256), losses := [] }

theorem u4563 : Upper (D 1) (R 1) [262,48,9,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4564 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 263 50 69 138 24 240 240 240 496), lower := (rows 263 50 69 138 24 32 64 128 256), losses := [] }

theorem u4564 : Upper (D 1) (R 1) [262,48,65,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4565 : PairBound 9 := { available := 216, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 69 138 48 248 216 216 472), lower := (rows 263 50 69 138 48 32 64 128 256), losses := [] }

theorem u4565 : Upper (D 1) (R 1) [262,48,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4565
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4566 : PairBound 9 := { available := 184, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 138 80 184 248 184 440), lower := (rows 263 50 69 138 80 32 64 128 256), losses := [] }

theorem u4566 : Upper (D 1) (R 1) [262,48,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4566
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4567_8 : Upper (D 1) (R 1) [262,48,65,130,128,8] 13 :=
  permutation_upper _ _ _ [262,48,65,130,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1287

theorem m4567_16 : Upper (D 1) (R 1) [262,48,65,130,128,16] 13 :=
  permutation_upper _ _ _ [262,48,65,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1288

theorem m4567_64 : Upper (D 1) (R 1) [262,48,65,130,128,64] 13 :=
  permutation_upper _ _ _ [262,48,65,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1289

def r4567 : Route 9 := (fun mask => (mask,id))

def c4567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4567 : Upper (D 1) (R 1) [262,48,65,130,128] 13 := by
  apply FastRouting.sound _ _ [262,48,65,130,128] 13 (by decide) (choices 1) [8,16,64] r4567 c4567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4567_8
  · exact m4567_16
  · exact m4567_64

def b4568 : PairBound 9 := { available := 232, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 152 18 232 232 232 488), lower := (rows 263 50 69 152 18 32 64 128 256), losses := [] }

theorem u4568 : Upper (D 1) (R 1) [262,48,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4569 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 263 50 69 152 24 226 226 226 482), lower := (rows 263 50 69 152 24 32 64 128 256), losses := [] }

theorem u4569 : Upper (D 1) (R 1) [262,48,65,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4570 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 69 152 48 234 202 202 458), lower := (rows 263 50 69 152 48 32 64 128 256), losses := [] }

theorem u4570 : Upper (D 1) (R 1) [262,48,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 170, camps := [{ cop := 4, region := 170, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 69 152 80 170 234 170 426), lower := (rows 263 50 69 152 80 32 64 128 256), losses := [] }

theorem u4571 : Upper (D 1) (R 1) [262,48,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4572 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 263 50 69 152 144 106 106 234 362), lower := (rows 263 50 69 152 144 32 64 128 256), losses := [] }

theorem u4572 : Upper (D 1) (R 1) [262,48,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4573 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 76 137 18 240 240 240 496), lower := (rows 263 50 76 137 18 32 64 128 256), losses := [] }

theorem u4573 : Upper (D 1) (R 1) [262,48,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4574 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 76 137 48 242 210 210 466), lower := (rows 263 50 76 137 48 32 64 128 256), losses := [] }

theorem u4574 : Upper (D 1) (R 1) [262,48,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 76 137 80 178 242 178 434), lower := (rows 263 50 76 137 80 32 64 128 256), losses := [] }

theorem u4575 : Upper (D 1) (R 1) [262,48,72,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4576 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 263 50 76 137 144 114 114 242 370), lower := (rows 263 50 76 137 144 32 64 128 256), losses := [] }

theorem u4576 : Upper (D 1) (R 1) [262,48,72,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4577 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 263 50 76 138 17 240 240 240 496), lower := (rows 263 50 76 138 17 32 64 128 256), losses := [] }

theorem u4577 : Upper (D 1) (R 1) [262,48,72,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 76 138 48 241 209 209 465), lower := (rows 263 50 76 138 48 32 64 128 256), losses := [] }

theorem u4578 : Upper (D 1) (R 1) [262,48,72,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4578
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4579_1 : Upper (D 1) (R 1) [262,48,72,130,64,1] 13 :=
  permutation_upper _ _ _ [262,48,72,130,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1290

theorem m4579_16 : Upper (D 1) (R 1) [262,48,72,130,64,16] 13 :=
  permutation_upper _ _ _ [262,48,72,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1292

def r4579 : Route 9 := (fun mask => (mask,id))

def c4579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4579 : Upper (D 1) (R 1) [262,48,72,130,64] 13 := by
  apply FastRouting.sound _ _ [262,48,72,130,64] 13 (by decide) (choices 1) [1,16,128] r4579 c4579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4579_1
  · exact m4579_16
  · exact u1294

theorem m4580_1 : Upper (D 1) (R 1) [262,48,72,130,128,1] 13 :=
  permutation_upper _ _ _ [262,48,72,130,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1291

theorem m4580_16 : Upper (D 1) (R 1) [262,48,72,130,128,16] 13 :=
  permutation_upper _ _ _ [262,48,72,130,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1293

theorem m4580_64 : Upper (D 1) (R 1) [262,48,72,130,128,64] 13 :=
  permutation_upper _ _ _ [262,48,72,130,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1294

def r4580 : Route 9 := (fun mask => (mask,id))

def c4580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4580 : Upper (D 1) (R 1) [262,48,72,130,128] 13 := by
  apply FastRouting.sound _ _ [262,48,72,130,128] 13 (by decide) (choices 1) [1,16,64] r4580 c4580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4580_1
  · exact m4580_16
  · exact m4580_64

def b4581 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 263 50 76 152 17 226 226 226 482), lower := (rows 263 50 76 152 17 32 64 128 256), losses := [] }

theorem u4581 : Upper (D 1) (R 1) [262,48,72,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4582 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 76 152 18 225 225 225 481), lower := (rows 263 50 76 152 18 32 64 128 256), losses := [] }

theorem u4582 : Upper (D 1) (R 1) [262,48,72,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4583 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 76 152 48 227 195 195 451), lower := (rows 263 50 76 152 48 32 64 128 256), losses := [] }

theorem u4583 : Upper (D 1) (R 1) [262,48,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4584 : Route 9 := (fun mask => (mask,id))

def c4584 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4584 : Upper (D 1) (R 1) [262,48,72,144,64] 13 := by
  apply FastRouting.sound _ _ [262,48,72,144,64] 13 (by decide) (choices 1) [1,2,128] r4584 c4584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1295
  · exact u1296
  · exact u1297

def b4585 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 263 50 76 152 144 99 99 227 355), lower := (rows 263 50 76 152 144 32 64 128 256), losses := [] }

theorem u4585 : Upper (D 1) (R 1) [262,48,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 263 50 196 25 18 232 232 232 488), lower := (rows 263 50 196 25 18 32 64 128 256), losses := [] }

theorem u4586 : Upper (D 1) (R 1) [262,48,192,17,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 263 50 196 25 24 226 226 226 482), lower := (rows 263 50 196 25 24 32 64 128 256), losses := [] }

theorem u4587 : Upper (D 1) (R 1) [262,48,192,17,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4587
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4588 : PairBound 9 := { available := 202, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 196 25 48 234 202 202 458), lower := (rows 263 50 196 25 48 32 64 128 256), losses := [] }

theorem u4588 : Upper (D 1) (R 1) [262,48,192,17,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4589 : PairBound 9 := { available := 170, camps := [{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 196 25 80 170 234 170 426), lower := (rows 263 50 196 25 80 32 64 128 256), losses := [] }

theorem u4589 : Upper (D 1) (R 1) [262,48,192,17,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 184, camps := [], pairs := [], upper := (rows 263 50 196 74 17 184 248 184 440), lower := (rows 263 50 196 74 17 32 64 128 256), losses := [] }

theorem u4590 : Upper (D 1) (R 1) [262,48,192,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 263 50 196 74 24 177 241 177 433), lower := (rows 263 50 196 74 24 32 64 128 256), losses := [] }

theorem u4591 : Upper (D 1) (R 1) [262,48,192,66,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 153, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 196 74 48 185 217 153 409), lower := (rows 263 50 196 74 48 32 64 128 256), losses := [] }

theorem u4592 : Upper (D 1) (R 1) [262,48,192,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4592
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4593_1 : Upper (D 1) (R 1) [262,48,192,66,128,1] 13 :=
  permutation_upper _ _ _ [262,48,192,66,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1298

theorem m4593_8 : Upper (D 1) (R 1) [262,48,192,66,128,8] 13 :=
  permutation_upper _ _ _ [262,48,192,66,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1299

theorem m4593_16 : Upper (D 1) (R 1) [262,48,192,66,128,16] 13 :=
  permutation_upper _ _ _ [262,48,192,66,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1300

def r4593 : Route 9 := (fun mask => (mask,id))

def c4593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4593 : Upper (D 1) (R 1) [262,48,192,66,128] 13 := by
  apply FastRouting.sound _ _ [262,48,192,66,128] 13 (by decide) (choices 1) [1,8,16] r4593 c4593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4593_1
  · exact m4593_8
  · exact m4593_16

def b4594 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 263 50 196 88 17 170 234 170 426), lower := (rows 263 50 196 88 17 32 64 128 256), losses := [] }

theorem u4594 : Upper (D 1) (R 1) [262,48,192,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4595 : PairBound 9 := { available := 169, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 263 50 196 88 18 169 233 169 425), lower := (rows 263 50 196 88 18 32 64 128 256), losses := [] }

theorem u4595 : Upper (D 1) (R 1) [262,48,192,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 263 50 196 88 24 163 227 163 419), lower := (rows 263 50 196 88 24 32 64 128 256), losses := [] }

theorem u4596 : Upper (D 1) (R 1) [262,48,192,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4597 : PairBound 9 := { available := 139, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 263 50 196 88 48 171 203 139 395), lower := (rows 263 50 196 88 48 32 64 128 256), losses := [] }

theorem u4597 : Upper (D 1) (R 1) [262,48,192,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4598 : PairBound 9 := { available := 43, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 263 50 196 88 144 43 107 171 299), lower := (rows 263 50 196 88 144 32 64 128 256), losses := [] }

theorem u4598 : Upper (D 1) (R 1) [262,48,192,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 269 19 38 74 48 240 208 208 464), lower := (rows 269 19 38 74 48 32 64 128 256), losses := [] }

theorem u4599 : Upper (D 1) (R 1) [268,17,34,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4599
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4600 : Route 9 := (fun mask => (mask,id))

def c4600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4600 : Upper (D 1) (R 1) [268,17,34,66,128] 13 := by
  apply FastRouting.sound _ _ [268,17,34,66,128] 13 (by decide) (choices 1) [16,64,128] r4600 c4600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1301
  · exact u1302
  · exact u1303

def b4601 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 18, targets := 32 }], pairs := [(1,5)], upper := (rows 269 19 38 200 18 240 240 240 496), lower := (rows 269 19 38 200 18 32 64 128 256), losses := [] }

theorem u4601 : Upper (D 1) (R 1) [268,17,34,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 269 19 38 200 48 242 210 210 466), lower := (rows 269 19 38 200 48 32 64 128 256), losses := [] }

theorem u4602 : Upper (D 1) (R 1) [268,17,34,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 178, camps := [{ cop := 1, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 269 19 38 200 80 178 242 178 434), lower := (rows 269 19 38 200 80 32 64 128 256), losses := [] }

theorem u4603 : Upper (D 1) (R 1) [268,17,34,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 7 74 48 240 208 208 464), lower := (rows 269 50 7 74 48 32 64 128 256), losses := [] }

theorem u4604 : Upper (D 1) (R 1) [268,48,3,66,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 74 80 176 240 176 432), lower := (rows 269 50 7 74 80 32 64 128 256), losses := [] }

theorem u4605 : Upper (D 1) (R 1) [268,48,3,66,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4605
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4606_16 : Upper (D 1) (R 1) [268,48,3,66,128,16] 13 :=
  permutation_upper _ _ _ [268,48,3,66,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1304

theorem m4606_64 : Upper (D 1) (R 1) [268,48,3,66,128,64] 13 :=
  permutation_upper _ _ _ [268,48,3,66,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1305

def r4606 : Route 9 := (fun mask => (mask,id))

def c4606 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u4606 : Upper (D 1) (R 1) [268,48,3,66,128] 13 := by
  apply FastRouting.sound _ _ [268,48,3,66,128] 13 (by decide) (choices 1) [16,64,128] r4606 c4606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4606_16
  · exact m4606_64
  · exact u1306

def b4607 : PairBound 9 := { available := 224, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 88 18 224 224 224 480), lower := (rows 269 50 7 88 18 32 64 128 256), losses := [] }

theorem u4607 : Upper (D 1) (R 1) [268,48,3,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4608 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 7 88 48 226 194 194 450), lower := (rows 269 50 7 88 48 32 64 128 256), losses := [] }

theorem u4608 : Upper (D 1) (R 1) [268,48,3,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4609 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 269 50 7 88 80 162 226 162 418), lower := (rows 269 50 7 88 80 32 64 128 256), losses := [] }

theorem u4609 : Upper (D 1) (R 1) [268,48,3,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4610 : Route 9 := (fun mask => (mask,id))

def c4610 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4610 : Upper (D 1) (R 1) [268,48,3,80,128] 13 := by
  apply FastRouting.sound _ _ [268,48,3,80,128] 13 (by decide) (choices 1) [2,64,128] r4610 c4610
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1307
  · exact u1308
  · exact u1309

def b4611 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 200 18 240 240 240 496), lower := (rows 269 50 7 200 18 32 64 128 256), losses := [] }

theorem u4611 : Upper (D 1) (R 1) [268,48,3,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 7 200 48 242 210 210 466), lower := (rows 269 50 7 200 48 32 64 128 256), losses := [] }

theorem u4612 : Upper (D 1) (R 1) [268,48,3,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4612
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 7 200 80 178 242 178 434), lower := (rows 269 50 7 200 80 32 64 128 256), losses := [] }

theorem u4613 : Upper (D 1) (R 1) [268,48,3,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 240, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 138 18 240 240 240 496), lower := (rows 269 50 69 138 18 32 64 128 256), losses := [] }

theorem u4614 : Upper (D 1) (R 1) [268,48,65,130,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 210, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 69 138 48 242 210 210 466), lower := (rows 269 50 69 138 48 32 64 128 256), losses := [] }

theorem u4615 : Upper (D 1) (R 1) [268,48,65,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 178, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 138 80 178 242 178 434), lower := (rows 269 50 69 138 80 32 64 128 256), losses := [] }

theorem u4616 : Upper (D 1) (R 1) [268,48,65,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 114, camps := [{ cop := 4, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 269 50 69 138 144 114 114 242 370), lower := (rows 269 50 69 138 144 32 64 128 256), losses := [] }

theorem u4617 : Upper (D 1) (R 1) [268,48,65,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 226, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 152 18 226 226 226 482), lower := (rows 269 50 69 152 18 32 64 128 256), losses := [] }

theorem u4618 : Upper (D 1) (R 1) [268,48,65,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 69 152 48 226 194 194 450), lower := (rows 269 50 69 152 48 32 64 128 256), losses := [] }

theorem u4619 : Upper (D 1) (R 1) [268,48,65,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4619
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P01
