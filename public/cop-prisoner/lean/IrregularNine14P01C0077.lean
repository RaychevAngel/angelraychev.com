import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0021
import IrregularNine14P01C0022

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4620 : PairBound 9 := { available := 162, camps := [{ cop := 4, region := 162, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 69 152 80 162 226 162 418), lower := (rows 269 50 69 152 80 32 64 128 256), losses := [] }

theorem u4620 : Upper (D 1) (R 1) [268,48,65,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4620
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4621 : PairBound 9 := { available := 98, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 269 50 69 152 144 98 98 226 354), lower := (rows 269 50 69 152 144 32 64 128 256), losses := [] }

theorem u4621 : Upper (D 1) (R 1) [268,48,65,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4621
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4622 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 269 50 70 138 17 240 240 240 496), lower := (rows 269 50 70 138 17 32 64 128 256), losses := [] }

theorem u4622 : Upper (D 1) (R 1) [268,48,66,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4622
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4623 : PairBound 9 := { available := 209, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 70 138 48 241 209 209 465), lower := (rows 269 50 70 138 48 32 64 128 256), losses := [] }

theorem u4623 : Upper (D 1) (R 1) [268,48,66,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4623
    (constants 1).1 (constants 1).2 (by decide +kernel)

theorem m4624_1 : Upper (D 1) (R 1) [268,48,66,130,64,1] 13 :=
  permutation_upper _ _ _ [268,48,66,130,1,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1310

theorem m4624_16 : Upper (D 1) (R 1) [268,48,66,130,64,16] 13 :=
  permutation_upper _ _ _ [268,48,66,130,32,64] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u1311

def r4624 : Route 9 := (fun mask => (mask,id))

def c4624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4624 : Upper (D 1) (R 1) [268,48,66,130,64] 13 := by
  apply FastRouting.sound _ _ [268,48,66,130,64] 13 (by decide) (choices 1) [1,16,128] r4624 c4624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m4624_1
  · exact m4624_16
  · exact u1312

def b4625 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 269 50 70 152 17 226 226 226 482), lower := (rows 269 50 70 152 17 32 64 128 256), losses := [] }

theorem u4625 : Upper (D 1) (R 1) [268,48,66,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4625
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4626 : PairBound 9 := { available := 225, camps := [{ cop := 5, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 70 152 18 225 225 225 481), lower := (rows 269 50 70 152 18 32 64 128 256), losses := [] }

theorem u4626 : Upper (D 1) (R 1) [268,48,66,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4626
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4627 : PairBound 9 := { available := 195, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 70 152 48 227 195 195 451), lower := (rows 269 50 70 152 48 32 64 128 256), losses := [] }

theorem u4627 : Upper (D 1) (R 1) [268,48,66,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4627
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4628 : Route 9 := (fun mask => (mask,id))

def c4628 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4628 : Upper (D 1) (R 1) [268,48,66,144,64] 13 := by
  apply FastRouting.sound _ _ [268,48,66,144,64] 13 (by decide) (choices 1) [1,2,128] r4628 c4628
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1313
  · exact u1314
  · exact u1315

def b4629 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 269 50 70 152 144 99 99 227 355), lower := (rows 269 50 70 152 144 32 64 128 256), losses := [] }

theorem u4629 : Upper (D 1) (R 1) [268,48,66,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4629
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4630 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 269 50 84 168 17 226 194 194 450), lower := (rows 269 50 84 168 17 32 64 128 256), losses := [] }

theorem u4630 : Upper (D 1) (R 1) [268,48,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4630
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4631 : PairBound 9 := { available := 195, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 84 168 18 227 195 195 451), lower := (rows 269 50 84 168 18 32 64 128 256), losses := [] }

theorem u4631 : Upper (D 1) (R 1) [268,48,80,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4631
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4632 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6)], upper := (rows 269 50 84 168 80 163 195 131 387), lower := (rows 269 50 84 168 80 32 64 128 256), losses := [] }

theorem u4632 : Upper (D 1) (R 1) [268,48,80,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4632
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4633 : PairBound 9 := { available := 67, camps := [{ cop := 3, region := 18, targets := 64 }], pairs := [(1,6)], upper := (rows 269 50 84 168 144 99 67 195 323), lower := (rows 269 50 84 168 144 32 64 128 256), losses := [] }

theorem u4633 : Upper (D 1) (R 1) [268,48,80,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4633
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4634 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 88 18 224 224 224 480), lower := (rows 275 7 44 88 18 32 64 128 256), losses := [] }

theorem u4634 : Upper (D 1) (R 1) [274,5,40,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4634
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4635 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 88 48 226 194 194 450), lower := (rows 275 7 44 88 48 32 64 128 256), losses := [] }

theorem u4635 : Upper (D 1) (R 1) [274,5,40,80,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4635
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4636 : PairBound 9 := { available := 162, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 275 7 44 88 80 162 226 162 418), lower := (rows 275 7 44 88 80 32 64 128 256), losses := [] }

theorem u4636 : Upper (D 1) (R 1) [274,5,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4636
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4637 : Route 9 := (fun mask => (mask,id))

def c4637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4637 : Upper (D 1) (R 1) [274,5,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,5,40,80,128] 13 (by decide) (choices 1) [2,64,128] r4637 c4637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1316
  · exact u1317
  · exact u1318

def b4638 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 44 200 18 240 240 240 496), lower := (rows 275 7 44 200 18 32 64 128 256), losses := [] }

theorem u4638 : Upper (D 1) (R 1) [274,5,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4638
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4639 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 44 200 48 242 210 210 466), lower := (rows 275 7 44 200 48 32 64 128 256), losses := [] }

theorem u4639 : Upper (D 1) (R 1) [274,5,40,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4639
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4640 : Route 9 := (fun mask => (mask,id))

def c4640 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4640 : Upper (D 1) (R 1) [274,5,40,192,64] 13 := by
  apply FastRouting.sound _ _ [274,5,40,192,64] 13 (by decide) (choices 1) [2,16,128] r4640 c4640
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1319
  · exact u1320
  · exact u1321

def b4641 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 56 18 232 200 200 456), lower := (rows 275 7 100 56 18 32 64 128 256), losses := [] }

theorem u4641 : Upper (D 1) (R 1) [274,5,96,48,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4641
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4642 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 7 100 56 24 226 194 194 450), lower := (rows 275 7 100 56 24 32 64 128 256), losses := [] }

theorem u4642 : Upper (D 1) (R 1) [274,5,96,48,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4642
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4643 : PairBound 9 := { available := 138, camps := [{ cop := 2, region := 24, targets := 2 }], pairs := [(3,1)], upper := (rows 275 7 100 56 80 170 202 138 394), lower := (rows 275 7 100 56 80 32 64 128 256), losses := [] }

theorem u4643 : Upper (D 1) (R 1) [274,5,96,48,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4643
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4644 : Route 9 := (fun mask => (mask,id))

def c4644 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4644 : Upper (D 1) (R 1) [274,5,96,48,128] 13 := by
  apply FastRouting.sound _ _ [274,5,96,48,128] 13 (by decide) (choices 1) [2,8,64,128] r4644 c4644
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1322
  · exact u1323
  · exact u1324
  · exact u1325

def b4645 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 152 18 232 232 232 488), lower := (rows 275 7 100 152 18 32 64 128 256), losses := [] }

theorem u4645 : Upper (D 1) (R 1) [274,5,96,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4645
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4646 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 275 7 100 152 24 226 226 226 482), lower := (rows 275 7 100 152 24 32 64 128 256), losses := [] }

theorem u4646 : Upper (D 1) (R 1) [274,5,96,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4646
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4647 : PairBound 9 := { available := 202, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 7 100 152 48 234 202 202 458), lower := (rows 275 7 100 152 48 32 64 128 256), losses := [] }

theorem u4647 : Upper (D 1) (R 1) [274,5,96,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4647
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4648 : PairBound 9 := { available := 106, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 275 7 100 152 144 106 106 234 362), lower := (rows 275 7 100 152 144 32 64 128 256), losses := [] }

theorem u4648 : Upper (D 1) (R 1) [274,5,96,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4648
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4649 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 7 100 168 18 248 216 216 472), lower := (rows 275 7 100 168 18 32 64 128 256), losses := [] }

theorem u4649 : Upper (D 1) (R 1) [274,5,96,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4649
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4650 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 7 100 168 24 242 210 210 466), lower := (rows 275 7 100 168 24 32 64 128 256), losses := [] }

theorem u4650 : Upper (D 1) (R 1) [274,5,96,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4650
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4651 : PairBound 9 := { available := 154, camps := [{ cop := 0, region := 168, targets := 64 }], pairs := [(3,6)], upper := (rows 275 7 100 168 80 186 218 154 410), lower := (rows 275 7 100 168 80 32 64 128 256), losses := [] }

theorem u4651 : Upper (D 1) (R 1) [274,5,96,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4651
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4652 : Route 9 := (fun mask => (mask,id))

def c4652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4652 : Upper (D 1) (R 1) [274,5,96,160,128] 13 := by
  apply FastRouting.sound _ _ [274,5,96,160,128] 13 (by decide) (choices 1) [2,8,16,64] r4652 c4652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1326
  · exact u1327
  · exact u1328
  · exact u1329

def b4653 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 228, targets := 2 }], pairs := [(2,1)], upper := (rows 275 14 37 200 18 240 240 240 496), lower := (rows 275 14 37 200 18 32 64 128 256), losses := [] }

theorem u4653 : Upper (D 1) (R 1) [274,12,33,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4653
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4654 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 200, targets := 32 }], pairs := [(3,5)], upper := (rows 275 14 37 200 48 242 210 210 466), lower := (rows 275 14 37 200 48 32 64 128 256), losses := [] }

theorem u4654 : Upper (D 1) (R 1) [274,12,33,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4654
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4655 : PairBound 9 := { available := 178, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 275 14 37 200 80 178 242 178 434), lower := (rows 275 14 37 200 80 32 64 128 256), losses := [] }

theorem u4655 : Upper (D 1) (R 1) [274,12,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4655
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4656 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 28 104 18 228 196 196 452), lower := (rows 275 35 28 104 18 32 64 128 256), losses := [] }

theorem u4656 : Upper (D 1) (R 1) [274,33,24,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4656
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4657 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 28 104 20 226 194 194 450), lower := (rows 275 35 28 104 20 32 64 128 256), losses := [] }

theorem u4657 : Upper (D 1) (R 1) [274,33,24,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4657
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4658 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 28 104 80 166 198 134 390), lower := (rows 275 35 28 104 80 32 64 128 256), losses := [] }

theorem u4658 : Upper (D 1) (R 1) [274,33,24,96,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4658
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4659 : Route 9 := (fun mask => (mask,id))

def c4659 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4659 : Upper (D 1) (R 1) [274,33,24,96,128] 13 := by
  apply FastRouting.sound _ _ [274,33,24,96,128] 13 (by decide) (choices 1) [2,4,64,128] r4659 c4659
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1330
  · exact u1331
  · exact u1332
  · exact u1333

def b4660 : PairBound 9 := { available := 228, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 28 200 18 228 228 228 484), lower := (rows 275 35 28 200 18 32 64 128 256), losses := [] }

theorem u4660 : Upper (D 1) (R 1) [274,33,24,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4660
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4661 : PairBound 9 := { available := 226, camps := [], pairs := [], upper := (rows 275 35 28 200 20 226 226 226 482), lower := (rows 275 35 28 200 20 32 64 128 256), losses := [] }

theorem u4661 : Upper (D 1) (R 1) [274,33,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4661
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4662 : PairBound 9 := { available := 198, camps := [{ cop := 0, region := 204, targets := 32 }], pairs := [(2,5)], upper := (rows 275 35 28 200 48 230 198 198 454), lower := (rows 275 35 28 200 48 32 64 128 256), losses := [] }

theorem u4662 : Upper (D 1) (R 1) [274,33,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4662
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4663 : PairBound 9 := { available := 166, camps := [{ cop := 3, region := 20, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 28 200 80 166 230 166 422), lower := (rows 275 35 28 200 80 32 64 128 256), losses := [] }

theorem u4663 : Upper (D 1) (R 1) [274,33,24,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4663
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4664 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 44 88 18 228 196 196 452), lower := (rows 275 35 44 88 18 32 64 128 256), losses := [] }

theorem u4664 : Upper (D 1) (R 1) [274,33,40,80,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4664
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4665 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 44 88 20 226 194 194 450), lower := (rows 275 35 44 88 20 32 64 128 256), losses := [] }

theorem u4665 : Upper (D 1) (R 1) [274,33,40,80,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4665
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4666 : PairBound 9 := { available := 134, camps := [{ cop := 3, region := 423, targets := 64 }], pairs := [(0,6)], upper := (rows 275 35 44 88 80 166 198 134 390), lower := (rows 275 35 44 88 80 32 64 128 256), losses := [] }

theorem u4666 : Upper (D 1) (R 1) [274,33,40,80,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4666
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4667 : Route 9 := (fun mask => (mask,id))

def c4667 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4667 : Upper (D 1) (R 1) [274,33,40,80,128] 13 := by
  apply FastRouting.sound _ _ [274,33,40,80,128] 13 (by decide) (choices 1) [2,4,64,128] r4667 c4667
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1334
  · exact u1335
  · exact u1336
  · exact u1337

def b4668 : PairBound 9 := { available := 212, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 44 200 18 244 212 212 468), lower := (rows 275 35 44 200 18 32 64 128 256), losses := [] }

theorem u4668 : Upper (D 1) (R 1) [274,33,40,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4668
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4669 : PairBound 9 := { available := 210, camps := [], pairs := [], upper := (rows 275 35 44 200 20 242 210 210 466), lower := (rows 275 35 44 200 20 32 64 128 256), losses := [] }

theorem u4669 : Upper (D 1) (R 1) [274,33,40,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4669
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4670 : Route 9 := (fun mask => (mask,id))

def c4670 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4670 : Upper (D 1) (R 1) [274,33,40,192,64] 13 := by
  apply FastRouting.sound _ _ [274,33,40,192,64] 13 (by decide) (choices 1) [2,4,16,128] r4670 c4670
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1338
  · exact u1339
  · exact u1340
  · exact u1341

def b4671 : PairBound 9 := { available := 200, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 76 18 232 200 200 456), lower := (rows 275 35 52 76 18 32 64 128 256), losses := [] }

theorem u4671 : Upper (D 1) (R 1) [274,33,48,68,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4671
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4672 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 275 35 52 76 24 226 194 194 450), lower := (rows 275 35 52 76 24 32 64 128 256), losses := [] }

theorem u4672 : Upper (D 1) (R 1) [274,33,48,68,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4672
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4673 : Route 9 := (fun mask => (mask,id))

def c4673 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4673 : Upper (D 1) (R 1) [274,33,48,68,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,64] 13 (by decide) (choices 1) [2,8,128] r4673 c4673
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1342
  · exact u1343
  · exact u1344

def r4674 : Route 9 := (fun mask => (mask,id))

def c4674 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 256 => 8 | _ => 0)

theorem u4674 : Upper (D 1) (R 1) [274,33,48,68,128] 13 := by
  apply FastRouting.sound _ _ [274,33,48,68,128] 13 (by decide) (choices 1) [2,8,64,128] r4674 c4674
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1345
  · exact u1346
  · exact u1347
  · exact u1348

def b4675 : PairBound 9 := { available := 204, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 200 18 236 204 204 460), lower := (rows 275 35 52 200 18 32 64 128 256), losses := [] }

theorem u4675 : Upper (D 1) (R 1) [274,33,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4675
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4676 : PairBound 9 := { available := 202, camps := [], pairs := [], upper := (rows 275 35 52 200 20 234 202 202 458), lower := (rows 275 35 52 200 20 32 64 128 256), losses := [] }

theorem u4676 : Upper (D 1) (R 1) [274,33,48,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4676
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b4677 : PairBound 9 := { available := 198, camps := [], pairs := [], upper := (rows 275 35 52 200 24 230 198 198 454), lower := (rows 275 35 52 200 24 32 64 128 256), losses := [] }

theorem u4677 : Upper (D 1) (R 1) [274,33,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4677
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r4678 : Route 9 := (fun mask => (mask,id))

def c4678 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u4678 : Upper (D 1) (R 1) [274,33,48,192,64] 13 := by
  apply FastRouting.sound _ _ [274,33,48,192,64] 13 (by decide) (choices 1) [2,4,8,128] r4678 c4678
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u1349
  · exact u1350
  · exact u1351
  · exact u1352

def b4679 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 236, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 140 18 240 240 240 496), lower := (rows 275 35 76 140 18 32 64 128 256), losses := [] }

theorem u4679 : Upper (D 1) (R 1) [274,33,72,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b4679
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u4679
end Delivery.IrregularNine14.P01
