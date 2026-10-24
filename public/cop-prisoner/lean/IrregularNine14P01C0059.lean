import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0014
import IrregularNine14P01C0015

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b3540 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 456, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 14 265 18 240 240 240 496), lower := (rows 53 194 14 265 18 32 64 128 256), losses := [] }

theorem u3540 : Upper (D 1) (R 1) [52,192,10,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3540
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3541 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 14 265 48 242 210 210 466), lower := (rows 53 194 14 265 48 32 64 128 256), losses := [] }

theorem u3541 : Upper (D 1) (R 1) [52,192,10,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3541
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3542_2 : Upper (D 1) (R 1) [52,192,10,257,64,2] 13 :=
  permutation_upper _ _ _ [52,192,10,257,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u880

theorem m3542_16 : Upper (D 1) (R 1) [52,192,10,257,64,16] 13 :=
  permutation_upper _ _ _ [52,192,10,257,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u881

def r3542 : Route 9 := (fun mask => (mask,id))

def c3542 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3542 : Upper (D 1) (R 1) [52,192,10,257,64] 13 := by
  apply FastRouting.sound _ _ [52,192,10,257,64] 13 (by decide) (choices 1) [2,16,128] r3542 c3542
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3542_2
  · exact m3542_16
  · exact u882

def b3543 : PairBound 9 := { available := 306, camps := [], pairs := [(3,6)], upper := (rows 53 194 76 137 18 306 370 434 306), lower := (rows 53 194 76 137 18 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 50 0 146 274), good := (rows 445 434 12 137 434 32 0 128 256) }] }

theorem u3543 : Upper (D 1) (R 1) [52,192,72,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3543
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3544 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 137 48 306 338 402 274), lower := (rows 53 194 76 137 48 32 64 128 256), losses := [] }

theorem u3544 : Upper (D 1) (R 1) [52,192,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3544
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3545 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 76 137 272 50 114 178 306), lower := (rows 53 194 76 137 272 32 64 128 256), losses := [] }

theorem u3545 : Upper (D 1) (R 1) [52,192,72,129,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3545
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3546 : PairBound 9 := { available := 178, camps := [], pairs := [(3,6)], upper := (rows 53 194 76 265 18 178 242 178 434), lower := (rows 53 194 76 265 18 32 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 18 50 0 146 274), good := (rows 445 434 12 265 434 32 0 128 256) }] }

theorem u3546 : Upper (D 1) (R 1) [52,192,72,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3546
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3547 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 265 48 178 210 146 402), lower := (rows 53 194 76 265 48 32 64 128 256), losses := [] }

theorem u3547 : Upper (D 1) (R 1) [52,192,72,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3547
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3548_2 : Upper (D 1) (R 1) [52,192,72,257,128,2] 13 :=
  permutation_upper _ _ _ [52,192,72,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u883

theorem m3548_16 : Upper (D 1) (R 1) [52,192,72,257,128,16] 13 :=
  permutation_upper _ _ _ [52,192,72,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u884

def r3548 : Route 9 := (fun mask => (mask,id))

def c3548 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3548 : Upper (D 1) (R 1) [52,192,72,257,128] 13 := by
  apply FastRouting.sound _ _ [52,192,72,257,128] 13 (by decide) (choices 1) [2,16] r3548 c3548
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3548_2
  · exact m3548_16

def b3549 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 194 76 266 17 178 242 178 434), lower := (rows 53 194 76 266 17 32 64 128 256), losses := [] }

theorem u3549 : Upper (D 1) (R 1) [52,192,72,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3549
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3550 : PairBound 9 := { available := 177, camps := [], pairs := [(0,6)], upper := (rows 53 194 76 266 18 177 241 177 433), lower := (rows 53 194 76 266 18 32 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 8 26 37 0 133 261), good := (rows 437 146 445 282 18 32 0 128 256) }] }

theorem u3550 : Upper (D 1) (R 1) [52,192,72,258,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3550
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3551 : PairBound 9 := { available := 147, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 266 48 179 211 147 403), lower := (rows 53 194 76 266 48 32 64 128 256), losses := [] }

theorem u3551 : Upper (D 1) (R 1) [52,192,72,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3551
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3552_1 : Upper (D 1) (R 1) [52,192,72,258,128,1] 13 :=
  permutation_upper _ _ _ [52,192,72,258,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u885

theorem m3552_2 : Upper (D 1) (R 1) [52,192,72,258,128,2] 13 :=
  permutation_upper _ _ _ [52,192,72,258,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u886

theorem m3552_16 : Upper (D 1) (R 1) [52,192,72,258,128,16] 13 :=
  permutation_upper _ _ _ [52,192,72,258,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u887

def r3552 : Route 9 := (fun mask => (mask,id))

def c3552 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3552 : Upper (D 1) (R 1) [52,192,72,258,128] 13 := by
  apply FastRouting.sound _ _ [52,192,72,258,128] 13 (by decide) (choices 1) [1,2,16] r3552 c3552
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3552_1
  · exact m3552_2
  · exact m3552_16

def b3553 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 76 392 17 50 114 178 306), lower := (rows 53 194 76 392 17 32 64 128 256), losses := [] }

theorem u3553 : Upper (D 1) (R 1) [52,192,72,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3553
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3554_1 : Upper (D 1) (R 1) [52,192,72,384,2,1] 13 :=
  permutation_upper _ _ _ [52,192,72,384,1,2] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u888

def r3554 : Route 9 := (fun mask => (mask,id))

def c3554 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3554 : Upper (D 1) (R 1) [52,192,72,384,2] 13 := by
  apply FastRouting.sound _ _ [52,192,72,384,2] 13 (by decide) (choices 1) [1,2,16] r3554 c3554
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3554_1
  · exact u889
  · exact u890

def b3555 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 76 392 48 51 83 147 275), lower := (rows 53 194 76 392 48 32 64 128 256), losses := [] }

theorem u3555 : Upper (D 1) (R 1) [52,192,72,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3555
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3556 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 53 194 262 11 24 240 240 240 496), lower := (rows 53 194 262 11 24 32 64 128 256), losses := [] }

theorem u3556 : Upper (D 1) (R 1) [52,192,258,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3556
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3557 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 11 48 248 216 216 472), lower := (rows 53 194 262 11 48 32 64 128 256), losses := [] }

theorem u3557 : Upper (D 1) (R 1) [52,192,258,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3557
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3558_8 : Upper (D 1) (R 1) [52,192,258,3,64,8] 13 :=
  permutation_upper _ _ _ [52,192,258,3,8,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u891

theorem m3558_16 : Upper (D 1) (R 1) [52,192,258,3,64,16] 13 :=
  permutation_upper _ _ _ [52,192,258,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u892

def r3558 : Route 9 := (fun mask => (mask,id))

def c3558 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3558 : Upper (D 1) (R 1) [52,192,258,3,64] 13 := by
  apply FastRouting.sound _ _ [52,192,258,3,64] 13 (by decide) (choices 1) [8,16,128] r3558 c3558
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3558_8
  · exact m3558_16
  · exact u893

def b3559 : PairBound 9 := { available := 232, camps := [], pairs := [], upper := (rows 53 194 262 26 17 232 232 232 488), lower := (rows 53 194 262 26 17 32 64 128 256), losses := [] }

theorem u3559 : Upper (D 1) (R 1) [52,192,258,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3559
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3560 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 53 194 262 26 24 225 225 225 481), lower := (rows 53 194 262 26 24 32 64 128 256), losses := [] }

theorem u3560 : Upper (D 1) (R 1) [52,192,258,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3560
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3561 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 26 48 233 201 201 457), lower := (rows 53 194 262 26 48 32 64 128 256), losses := [] }

theorem u3561 : Upper (D 1) (R 1) [52,192,258,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3562 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 194 262 26 80 169 233 169 425), lower := (rows 53 194 262 26 80 32 64 128 256), losses := [] }

theorem u3562 : Upper (D 1) (R 1) [52,192,258,18,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3563 : PairBound 9 := { available := 184, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 262 73 18 184 248 184 440), lower := (rows 53 194 262 73 18 32 64 128 256), losses := [] }

theorem u3563 : Upper (D 1) (R 1) [52,192,258,65,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3564 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 194 262 73 24 178 242 178 434), lower := (rows 53 194 262 73 24 32 64 128 256), losses := [] }

theorem u3564 : Upper (D 1) (R 1) [52,192,258,65,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3565 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 73 48 186 218 154 410), lower := (rows 53 194 262 73 48 32 64 128 256), losses := [] }

theorem u3565 : Upper (D 1) (R 1) [52,192,258,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3565
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3566_2 : Upper (D 1) (R 1) [52,192,258,65,128,2] 13 :=
  permutation_upper _ _ _ [52,192,258,65,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u894

theorem m3566_8 : Upper (D 1) (R 1) [52,192,258,65,128,8] 13 :=
  permutation_upper _ _ _ [52,192,258,65,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u895

theorem m3566_16 : Upper (D 1) (R 1) [52,192,258,65,128,16] 13 :=
  permutation_upper _ _ _ [52,192,258,65,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u896

def r3566 : Route 9 := (fun mask => (mask,id))

def c3566 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3566 : Upper (D 1) (R 1) [52,192,258,65,128] 13 := by
  apply FastRouting.sound _ _ [52,192,258,65,128] 13 (by decide) (choices 1) [2,8,16] r3566 c3566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3566_2
  · exact m3566_8
  · exact m3566_16

def b3567 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 194 262 88 17 170 234 170 426), lower := (rows 53 194 262 88 17 32 64 128 256), losses := [] }

theorem u3567 : Upper (D 1) (R 1) [52,192,258,80,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3568 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 194 262 88 18 169 233 169 425), lower := (rows 53 194 262 88 18 32 64 128 256), losses := [] }

theorem u3568 : Upper (D 1) (R 1) [52,192,258,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3569 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 194 262 88 24 163 227 163 419), lower := (rows 53 194 262 88 24 32 64 128 256), losses := [] }

theorem u3569 : Upper (D 1) (R 1) [52,192,258,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3570 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 262 88 48 171 203 139 395), lower := (rows 53 194 262 88 48 32 64 128 256), losses := [] }

theorem u3570 : Upper (D 1) (R 1) [52,192,258,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3571 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 53 194 262 88 144 43 107 171 299), lower := (rows 53 194 262 88 144 32 64 128 256), losses := [] }

theorem u3571 : Upper (D 1) (R 1) [52,192,258,80,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3572 : PairBound 9 := { available := 240, camps := [], pairs := [(2,1)], upper := (rows 53 194 268 11 18 240 240 240 496), lower := (rows 53 194 268 11 18 32 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 16 49 81 145 273), good := (rows 501 192 268 493 496 32 64 128 256) }] }

theorem u3572 : Upper (D 1) (R 1) [52,192,264,3,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3573 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 268 11 48 242 210 210 466), lower := (rows 53 194 268 11 48 32 64 128 256), losses := [] }

theorem u3573 : Upper (D 1) (R 1) [52,192,264,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3573
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3574_2 : Upper (D 1) (R 1) [52,192,264,3,64,2] 13 :=
  permutation_upper _ _ _ [52,192,264,3,2,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u897

theorem m3574_16 : Upper (D 1) (R 1) [52,192,264,3,64,16] 13 :=
  permutation_upper _ _ _ [52,192,264,3,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u898

def r3574 : Route 9 := (fun mask => (mask,id))

def c3574 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3574 : Upper (D 1) (R 1) [52,192,264,3,64] 13 := by
  apply FastRouting.sound _ _ [52,192,264,3,64] 13 (by decide) (choices 1) [2,16,128] r3574 c3574
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3574_2
  · exact m3574_16
  · exact u899

def r3575 : Route 9 := (fun mask => (mask,id))

def c3575 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3575 : Upper (D 1) (R 1) [52,192,264,65,2] 13 := by
  apply FastRouting.sound _ _ [52,192,264,65,2] 13 (by decide) (choices 1) [2,16,128] r3575 c3575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u900
  · exact u901
  · exact u902

def b3576 : PairBound 9 := { available := 146, camps := [{ cop := 0, region := 194, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 268 73 48 178 210 146 402), lower := (rows 53 194 268 73 48 32 64 128 256), losses := [] }

theorem u3576 : Upper (D 1) (R 1) [52,192,264,65,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3576
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3577_2 : Upper (D 1) (R 1) [52,192,264,65,128,2] 13 :=
  permutation_upper _ _ _ [52,192,264,65,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u902

theorem m3577_16 : Upper (D 1) (R 1) [52,192,264,65,128,16] 13 :=
  permutation_upper _ _ _ [52,192,264,65,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u903

def r3577 : Route 9 := (fun mask => (mask,id))

def c3577 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3577 : Upper (D 1) (R 1) [52,192,264,65,128] 13 := by
  apply FastRouting.sound _ _ [52,192,264,65,128] 13 (by decide) (choices 1) [2,16] r3577 c3577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m3577_2
  · exact m3577_16

def r3578 : Route 9 := (fun mask => (mask,id))

def c3578 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 256 => 8 | _ => 0)

theorem u3578 : Upper (D 1) (R 1) [52,192,320,3,2] 13 := by
  apply FastRouting.sound _ _ [52,192,320,3,2] 13 (by decide) (choices 1) [8,16,128] r3578 c3578
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u904
  · exact u905
  · exact u906

def b3579 : PairBound 9 := { available := 178, camps := [], pairs := [], upper := (rows 53 194 324 11 24 178 242 178 434), lower := (rows 53 194 324 11 24 32 64 128 256), losses := [] }

theorem u3579 : Upper (D 1) (R 1) [52,192,320,3,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3579
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3580 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 11 48 186 218 154 410), lower := (rows 53 194 324 11 48 32 64 128 256), losses := [] }

theorem u3580 : Upper (D 1) (R 1) [52,192,320,3,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3580
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m3581_2 : Upper (D 1) (R 1) [52,192,320,3,128,2] 13 :=
  permutation_upper _ _ _ [52,192,320,3,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u906

theorem m3581_8 : Upper (D 1) (R 1) [52,192,320,3,128,8] 13 :=
  permutation_upper _ _ _ [52,192,320,3,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u907

theorem m3581_16 : Upper (D 1) (R 1) [52,192,320,3,128,16] 13 :=
  permutation_upper _ _ _ [52,192,320,3,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u908

def r3581 : Route 9 := (fun mask => (mask,id))

def c3581 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3581 : Upper (D 1) (R 1) [52,192,320,3,128] 13 := by
  apply FastRouting.sound _ _ [52,192,320,3,128] 13 (by decide) (choices 1) [2,8,16] r3581 c3581
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m3581_2
  · exact m3581_8
  · exact m3581_16

def b3582 : PairBound 9 := { available := 170, camps := [], pairs := [], upper := (rows 53 194 324 26 17 170 234 170 426), lower := (rows 53 194 324 26 17 32 64 128 256), losses := [] }

theorem u3582 : Upper (D 1) (R 1) [52,192,320,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3583 : PairBound 9 := { available := 169, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 194 324 26 18 169 233 169 425), lower := (rows 53 194 324 26 18 32 64 128 256), losses := [] }

theorem u3583 : Upper (D 1) (R 1) [52,192,320,18,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3584 : PairBound 9 := { available := 163, camps := [], pairs := [], upper := (rows 53 194 324 26 24 163 227 163 419), lower := (rows 53 194 324 26 24 32 64 128 256), losses := [] }

theorem u3584 : Upper (D 1) (R 1) [52,192,320,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3585 : PairBound 9 := { available := 139, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 26 48 171 203 139 395), lower := (rows 53 194 324 26 48 32 64 128 256), losses := [] }

theorem u3585 : Upper (D 1) (R 1) [52,192,320,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3586 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 194 324 26 144 43 107 171 299), lower := (rows 53 194 324 26 144 32 64 128 256), losses := [] }

theorem u3586 : Upper (D 1) (R 1) [52,192,320,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r3587 : Route 9 := (fun mask => (mask,id))

def c3587 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u3587 : Upper (D 1) (R 1) [52,192,320,129,2] 13 := by
  apply FastRouting.sound _ _ [52,192,320,129,2] 13 (by decide) (choices 1) [2,8,16] r3587 c3587
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u909
  · exact u910
  · exact u911

def b3588 : PairBound 9 := { available := 50, camps := [], pairs := [], upper := (rows 53 194 324 137 24 50 114 178 306), lower := (rows 53 194 324 137 24 32 64 128 256), losses := [] }

theorem u3588 : Upper (D 1) (R 1) [52,192,320,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3589 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 137 48 58 90 154 282), lower := (rows 53 194 324 137 48 32 64 128 256), losses := [] }

theorem u3589 : Upper (D 1) (R 1) [52,192,320,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3590 : PairBound 9 := { available := 42, camps := [], pairs := [], upper := (rows 53 194 324 152 17 42 106 170 298), lower := (rows 53 194 324 152 17 32 64 128 256), losses := [] }

theorem u3590 : Upper (D 1) (R 1) [52,192,320,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3591 : PairBound 9 := { available := 43, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 194 324 152 18 43 107 171 299), lower := (rows 53 194 324 152 18 32 64 128 256), losses := [] }

theorem u3591 : Upper (D 1) (R 1) [52,192,320,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3592 : PairBound 9 := { available := 35, camps := [], pairs := [], upper := (rows 53 194 324 152 24 35 99 163 291), lower := (rows 53 194 324 152 24 32 64 128 256), losses := [] }

theorem u3592 : Upper (D 1) (R 1) [52,192,320,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3593 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 202, targets := 32 }], pairs := [(1,5)], upper := (rows 53 194 324 152 48 43 75 139 267), lower := (rows 53 194 324 152 48 32 64 128 256), losses := [] }

theorem u3593 : Upper (D 1) (R 1) [52,192,320,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3594 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 53 259 14 200 18 240 240 240 496), lower := (rows 53 259 14 200 18 32 64 128 256), losses := [] }

theorem u3594 : Upper (D 1) (R 1) [52,257,10,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3595 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 450, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 14 200 48 242 210 210 466), lower := (rows 53 259 14 200 48 32 64 128 256), losses := [] }

theorem u3595 : Upper (D 1) (R 1) [52,257,10,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3596 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 386, targets := 64 }], pairs := [(1,6)], upper := (rows 53 259 14 200 80 178 242 178 434), lower := (rows 53 259 14 200 80 32 64 128 256), losses := [] }

theorem u3596 : Upper (D 1) (R 1) [52,257,10,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3597 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 53 259 70 88 18 168 232 168 424), lower := (rows 53 259 70 88 18 32 64 128 256), losses := [] }

theorem u3597 : Upper (D 1) (R 1) [52,257,66,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3598 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 53 259 70 88 24 162 226 162 418), lower := (rows 53 259 70 88 24 32 64 128 256), losses := [] }

theorem u3598 : Upper (D 1) (R 1) [52,257,66,80,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b3599 : PairBound 9 := { available := 138, camps := [{ cop := 0, region := 458, targets := 32 }], pairs := [(1,5)], upper := (rows 53 259 70 88 48 170 202 138 394), lower := (rows 53 259 70 88 48 32 64 128 256), losses := [] }

theorem u3599 : Upper (D 1) (R 1) [52,257,66,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b3599
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u3599
end Delivery.IrregularNine14.P01
