import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0027

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b4560 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 152 274 33 77 141 269), lower := (rows 35 70 44 152 274 33 64 128 256), losses := [] }

theorem u4560 : Upper (D 5) (R 5) [34,68,40,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4560
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4561 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 152 274 36 73 137 265), lower := (rows 35 70 44 152 274 36 64 128 256), losses := [] }

theorem u4561 : Upper (D 5) (R 5) [34,68,40,144,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4561
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4562 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 274 40 69 133 261), lower := (rows 35 70 44 152 274 40 64 128 256), losses := [] }

theorem u4562 : Upper (D 5) (R 5) [34,68,40,144,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4562
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4563 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 152 276 33 75 139 267), lower := (rows 35 70 44 152 276 33 64 128 256), losses := [] }

theorem u4563 : Upper (D 5) (R 5) [34,68,40,144,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4563
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4564 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 152 276 34 73 137 265), lower := (rows 35 70 44 152 276 34 64 128 256), losses := [] }

theorem u4564 : Upper (D 5) (R 5) [34,68,40,144,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4564
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4565 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 44 152 276 40 67 131 259), lower := (rows 35 70 44 152 276 40 64 128 256), losses := [] }

theorem u4565 : Upper (D 5) (R 5) [34,68,40,144,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4565
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4566 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 392 25 33 86 150 278), lower := (rows 35 70 44 392 25 33 64 128 256), losses := [] }

theorem u4566 : Upper (D 5) (R 5) [34,68,40,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4566
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4567 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 44 392 25 34 85 149 277), lower := (rows 35 70 44 392 25 34 64 128 256), losses := [] }

theorem u4567 : Upper (D 5) (R 5) [34,68,40,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4567
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4568 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 392 25 36 83 147 275), lower := (rows 35 70 44 392 25 36 64 128 256), losses := [] }

theorem u4568 : Upper (D 5) (R 5) [34,68,40,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4568
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4569 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3)], upper := (rows 35 70 44 392 25 48 71 135 263), lower := (rows 35 70 44 392 25 48 64 128 256), losses := [] }

theorem u4569 : Upper (D 5) (R 5) [34,68,40,384,9,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4569
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4570 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 44 392 26 33 85 149 277), lower := (rows 35 70 44 392 26 33 64 128 256), losses := [] }

theorem u4570 : Upper (D 5) (R 5) [34,68,40,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4570
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4571 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 44 392 26 36 81 145 273), lower := (rows 35 70 44 392 26 36 64 128 256), losses := [] }

theorem u4571 : Upper (D 5) (R 5) [34,68,40,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4571
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4572 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 44 392 26 48 69 133 261), lower := (rows 35 70 44 392 26 48 64 128 256), losses := [] }

theorem u4572 : Upper (D 5) (R 5) [34,68,40,384,10,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4572
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4573 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 137 26 33 332 396 268), lower := (rows 35 70 52 137 26 33 64 128 256), losses := [] }

theorem u4573 : Upper (D 5) (R 5) [34,68,48,129,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4573
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4574 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 137 26 36 329 393 265), lower := (rows 35 70 52 137 26 36 64 128 256), losses := [] }

theorem u4574 : Upper (D 5) (R 5) [34,68,48,129,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4574
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4575 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 137 26 40 325 389 261), lower := (rows 35 70 52 137 26 40 64 128 256), losses := [] }

theorem u4575 : Upper (D 5) (R 5) [34,68,48,129,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4575
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4576 : Route 9 := (fun mask => (mask,id))

def c4576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4576 : Upper (D 5) (R 5) [34,68,48,129,10,256] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,10,256] 13 (by decide) (choices 1) [1,4,8] r4576 c4576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1637
  · exact u1638
  · exact u1639

def b4577 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 137 273 34 76 140 268), lower := (rows 35 70 52 137 273 34 64 128 256), losses := [] }

theorem u4577 : Upper (D 5) (R 5) [34,68,48,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4577
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4578 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 137 273 36 74 138 266), lower := (rows 35 70 52 137 273 36 64 128 256), losses := [] }

theorem u4578 : Upper (D 5) (R 5) [34,68,48,129,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4578
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4579 : Route 9 := (fun mask => (mask,id))

def c4579 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4579 : Upper (D 5) (R 5) [34,68,48,129,257,8] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,257,8] 13 (by decide) (choices 1) [2,4,8] r4579 c4579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1640
  · exact u1641
  · exact u1642

def b4580 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 137 274 33 76 140 268), lower := (rows 35 70 52 137 274 33 64 128 256), losses := [] }

theorem u4580 : Upper (D 5) (R 5) [34,68,48,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4580
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4581 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 137 274 36 73 137 265), lower := (rows 35 70 52 137 274 36 64 128 256), losses := [] }

theorem u4581 : Upper (D 5) (R 5) [34,68,48,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4581
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4582 : Route 9 := (fun mask => (mask,id))

def c4582 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4582 : Upper (D 5) (R 5) [34,68,48,129,258,8] 13 := by
  apply FastRouting.sound _ _ [34,68,48,129,258,8] 13 (by decide) (choices 1) [1,4,8] r4582 c4582
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1643
  · exact u1644
  · exact u1645

def b4583 : PairBound 9 := { available := 14, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 137 280 33 78 142 270), lower := (rows 35 70 52 137 280 33 64 128 256), losses := [] }

theorem u4583 : Upper (D 5) (R 5) [34,68,48,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4583
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4584 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 137 280 34 77 141 269), lower := (rows 35 70 52 137 280 34 64 128 256), losses := [] }

theorem u4584 : Upper (D 5) (R 5) [34,68,48,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4584
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4585 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 137 280 36 75 139 267), lower := (rows 35 70 52 137 280 36 64 128 256), losses := [] }

theorem u4585 : Upper (D 5) (R 5) [34,68,48,129,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4585
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4586 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 137 280 40 71 135 263), lower := (rows 35 70 52 137 280 40 64 128 256), losses := [] }

theorem u4586 : Upper (D 5) (R 5) [34,68,48,129,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4586
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4587 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 52 138 25 33 332 396 268), lower := (rows 35 70 52 138 25 33 64 128 256), losses := [] }

theorem u4587 : Upper (D 5) (R 5) [34,68,48,130,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4587
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4588 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 138 25 36 329 393 265), lower := (rows 35 70 52 138 25 36 64 128 256), losses := [] }

theorem u4588 : Upper (D 5) (R 5) [34,68,48,130,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4588
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4589 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 138 25 40 325 389 261), lower := (rows 35 70 52 138 25 40 64 128 256), losses := [] }

theorem u4589 : Upper (D 5) (R 5) [34,68,48,130,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4589
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4590 : PairBound 9 := { available := 13, camps := [{ cop := 4, region := 292, targets := 2 }], pairs := [(2,1)], upper := (rows 35 70 52 138 25 288 77 141 269), lower := (rows 35 70 52 138 25 288 64 128 256), losses := [] }

theorem u4590 : Upper (D 5) (R 5) [34,68,48,130,9,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4590
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4591 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 52 138 273 33 76 140 268), lower := (rows 35 70 52 138 273 33 64 128 256), losses := [] }

theorem u4591 : Upper (D 5) (R 5) [34,68,48,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4591
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4592 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 138 273 36 73 137 265), lower := (rows 35 70 52 138 273 36 64 128 256), losses := [] }

theorem u4592 : Upper (D 5) (R 5) [34,68,48,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4592
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4593 : Route 9 := (fun mask => (mask,id))

def c4593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4593 : Upper (D 5) (R 5) [34,68,48,130,257,8] 13 := by
  apply FastRouting.sound _ _ [34,68,48,130,257,8] 13 (by decide) (choices 1) [1,4,8] r4593 c4593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1646
  · exact u1647
  · exact u1648

def b4594 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 138 280 33 77 141 269), lower := (rows 35 70 52 138 280 33 64 128 256), losses := [] }

theorem u4594 : Upper (D 5) (R 5) [34,68,48,130,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4594
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4595 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 136, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 138 280 36 73 137 265), lower := (rows 35 70 52 138 280 36 64 128 256), losses := [] }

theorem u4595 : Upper (D 5) (R 5) [34,68,48,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4595
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4596 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 138 280 40 69 133 261), lower := (rows 35 70 52 138 280 40 64 128 256), losses := [] }

theorem u4596 : Upper (D 5) (R 5) [34,68,48,130,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4596
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4597 : PairBound 9 := { available := 266, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 52 140 25 33 330 394 266), lower := (rows 35 70 52 140 25 33 64 128 256), losses := [] }

theorem u4597 : Upper (D 5) (R 5) [34,68,48,132,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4597
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4598 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 140 25 34 329 393 265), lower := (rows 35 70 52 140 25 34 64 128 256), losses := [] }

theorem u4598 : Upper (D 5) (R 5) [34,68,48,132,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4598
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4599 : PairBound 9 := { available := 259, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 140 25 40 323 387 259), lower := (rows 35 70 52 140 25 40 64 128 256), losses := [] }

theorem u4599 : Upper (D 5) (R 5) [34,68,48,132,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4599
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4600 : Route 9 := (fun mask => (mask,id))

def c4600 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4600 : Upper (D 5) (R 5) [34,68,48,132,9,256] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,9,256] 13 (by decide) (choices 1) [1,2,8] r4600 c4600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1649
  · exact u1650
  · exact u1651

def b4601 : PairBound 9 := { available := 265, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 140 26 33 329 393 265), lower := (rows 35 70 52 140 26 33 64 128 256), losses := [] }

theorem u4601 : Upper (D 5) (R 5) [34,68,48,132,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4601
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4602 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 323, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 140 26 40 321 385 257), lower := (rows 35 70 52 140 26 40 64 128 256), losses := [] }

theorem u4602 : Upper (D 5) (R 5) [34,68,48,132,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4602
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4603 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 289, targets := 4 }], pairs := [(0,2)], upper := (rows 35 70 52 140 26 288 73 137 265), lower := (rows 35 70 52 140 26 288 64 128 256), losses := [] }

theorem u4603 : Upper (D 5) (R 5) [34,68,48,132,10,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4603
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4604 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 202, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 52 140 273 33 74 138 266), lower := (rows 35 70 52 140 273 33 64 128 256), losses := [] }

theorem u4604 : Upper (D 5) (R 5) [34,68,48,132,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4604
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4605 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 140 273 34 73 137 265), lower := (rows 35 70 52 140 273 34 64 128 256), losses := [] }

theorem u4605 : Upper (D 5) (R 5) [34,68,48,132,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4605
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4606 : Route 9 := (fun mask => (mask,id))

def c4606 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4606 : Upper (D 5) (R 5) [34,68,48,132,257,8] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,257,8] 13 (by decide) (choices 1) [1,2,8] r4606 c4606
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1652
  · exact u1653
  · exact u1654

def b4607 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 140 274 33 73 137 265), lower := (rows 35 70 52 140 274 33 64 128 256), losses := [] }

theorem u4607 : Upper (D 5) (R 5) [34,68,48,132,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4607
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r4608 : Route 9 := (fun mask => (mask,id))

def c4608 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u4608 : Upper (D 5) (R 5) [34,68,48,132,258,8] 13 := by
  apply FastRouting.sound _ _ [34,68,48,132,258,8] 13 (by decide) (choices 1) [1,8] r4608 c4608
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u1655
  · exact u1656

def b4609 : PairBound 9 := { available := 11, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 140 280 33 75 139 267), lower := (rows 35 70 52 140 280 33 64 128 256), losses := [] }

theorem u4609 : Upper (D 5) (R 5) [34,68,48,132,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4609
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4610 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 140 280 34 73 137 265), lower := (rows 35 70 52 140 280 34 64 128 256), losses := [] }

theorem u4610 : Upper (D 5) (R 5) [34,68,48,132,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4610
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4611 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 140 280 40 67 131 259), lower := (rows 35 70 52 140 280 40 64 128 256), losses := [] }

theorem u4611 : Upper (D 5) (R 5) [34,68,48,132,264,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4611
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4612 : PairBound 9 := { available := 14, camps := [{ cop := 2, region := 458, targets := 33 }], pairs := [(1,0),(1,5)], upper := (rows 35 70 52 392 25 33 78 142 270), lower := (rows 35 70 52 392 25 33 64 128 256), losses := [] }

theorem u4612 : Upper (D 5) (R 5) [34,68,48,384,9,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4612
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4613 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 412, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 35 70 52 392 25 34 77 141 269), lower := (rows 35 70 52 392 25 34 64 128 256), losses := [] }

theorem u4613 : Upper (D 5) (R 5) [34,68,48,384,9,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4613
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4614 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 392 25 36 75 139 267), lower := (rows 35 70 52 392 25 36 64 128 256), losses := [] }

theorem u4614 : Upper (D 5) (R 5) [34,68,48,384,9,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4614
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4615 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 392 25 40 71 135 263), lower := (rows 35 70 52 392 25 40 64 128 256), losses := [] }

theorem u4615 : Upper (D 5) (R 5) [34,68,48,384,9,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4615
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4616 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 52 392 26 33 77 141 269), lower := (rows 35 70 52 392 26 33 64 128 256), losses := [] }

theorem u4616 : Upper (D 5) (R 5) [34,68,48,384,10,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4616
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4617 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 392, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 35 70 52 392 26 36 73 137 265), lower := (rows 35 70 52 392 26 36 64 128 256), losses := [] }

theorem u4617 : Upper (D 5) (R 5) [34,68,48,384,10,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4617
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4618 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 67, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 35 70 52 392 26 40 69 133 261), lower := (rows 35 70 52 392 26 40 64 128 256), losses := [] }

theorem u4618 : Upper (D 5) (R 5) [34,68,48,384,10,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4618
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b4619 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 33, targets := 12 }], pairs := [(0,2),(0,3)], upper := (rows 35 70 133 56 28 33 330 394 266), lower := (rows 35 70 133 56 28 33 64 128 256), losses := [] }

theorem u4619 : Upper (D 5) (R 5) [34,68,129,48,12,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b4619
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u4619
end Delivery.IrregularNine14.P05
