import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0007
import IrregularNine14P00C0008

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 28 200 20 161 225 161 417), lower := (rows 51 322 28 200 20 32 64 128 256), losses := [] }

theorem u1560 : Upper (D 0) (R 0) [50,320,24,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1560
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 28 200 48 165 197 133 389), lower := (rows 51 322 28 200 48 32 64 128 256), losses := [] }

theorem u1561 : Upper (D 0) (R 0) [50,320,24,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1561
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 20, targets := 1 }], pairs := [(2,0)], upper := (rows 51 322 28 200 144 37 101 165 293), lower := (rows 51 322 28 200 144 32 64 128 256), losses := [] }

theorem u1562 : Upper (D 0) (R 0) [50,320,24,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1562
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1563 : Route 9 := (fun mask => (mask,id))

def c1563 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1563 : Upper (D 0) (R 0) [50,320,72,129,1] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129,1] 13 (by decide) (choices 1) [4,16,128] r1563 c1563
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u479
  · exact u480
  · exact u481

def b1564 : PairBound 9 := { available := 177, camps := [], pairs := [], upper := (rows 51 322 76 137 20 177 241 177 433), lower := (rows 51 322 76 137 20 32 64 128 256), losses := [] }

theorem u1564 : Upper (D 0) (R 0) [50,320,72,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1564
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 149, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 137 48 181 213 149 405), lower := (rows 51 322 76 137 48 32 64 128 256), losses := [] }

theorem u1565 : Upper (D 0) (R 0) [50,320,72,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1565
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1566_1 : Upper (D 0) (R 0) [50,320,72,129,128,1] 13 :=
  permutation_upper _ _ _ [50,320,72,129,1,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u481

theorem m1566_4 : Upper (D 0) (R 0) [50,320,72,129,128,4] 13 :=
  permutation_upper _ _ _ [50,320,72,129,4,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u482

theorem m1566_16 : Upper (D 0) (R 0) [50,320,72,129,128,16] 13 :=
  permutation_upper _ _ _ [50,320,72,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u483

def r1566 : Route 9 := (fun mask => (mask,id))

def c1566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1566 : Upper (D 0) (R 0) [50,320,72,129,128] 13 := by
  apply FastRouting.sound _ _ [50,320,72,129,128] 13 (by decide) (choices 1) [1,4,16] r1566 c1566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1566_1
  · exact m1566_4
  · exact m1566_16

def r1567 : Route 9 := (fun mask => (mask,id))

def c1567 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1567 : Upper (D 0) (R 0) [50,320,72,144,1] 13 := by
  apply FastRouting.sound _ _ [50,320,72,144,1] 13 (by decide) (choices 1) [1,4,128] r1567 c1567
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u484
  · exact u485
  · exact u486

def b1568 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 76 152 20 161 225 161 417), lower := (rows 51 322 76 152 20 32 64 128 256), losses := [] }

theorem u1568 : Upper (D 0) (R 0) [50,320,72,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1568
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 76 152 48 165 197 133 389), lower := (rows 51 322 76 152 48 32 64 128 256), losses := [] }

theorem u1569 : Upper (D 0) (R 0) [50,320,72,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1569
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 51 322 76 152 144 37 101 165 293), lower := (rows 51 322 76 152 144 32 64 128 256), losses := [] }

theorem u1570 : Upper (D 0) (R 0) [50,320,72,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1570
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1571 : Route 9 := (fun mask => (mask,id))

def c1571 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1571 : Upper (D 0) (R 0) [50,320,80,129,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129,1] 13 (by decide) (choices 1) [4,8,128] r1571 c1571
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u487
  · exact u488
  · exact u489

def b1572 : PairBound 9 := { available := 169, camps := [], pairs := [], upper := (rows 51 322 84 137 20 169 233 169 425), lower := (rows 51 322 84 137 20 32 64 128 256), losses := [] }

theorem u1572 : Upper (D 0) (R 0) [50,320,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1572
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 165, camps := [], pairs := [], upper := (rows 51 322 84 137 24 165 229 165 421), lower := (rows 51 322 84 137 24 32 64 128 256), losses := [] }

theorem u1573 : Upper (D 0) (R 0) [50,320,80,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1573
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 141, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 84 137 48 173 205 141 397), lower := (rows 51 322 84 137 48 32 64 128 256), losses := [] }

theorem u1574 : Upper (D 0) (R 0) [50,320,80,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1574
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1575 : Route 9 := (fun mask => (mask,id))

def c1575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1575 : Upper (D 0) (R 0) [50,320,80,129,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,129,128] 13 (by decide) (choices 1) [1,4,8] r1575 c1575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u490
  · exact u491
  · exact u492

def r1576 : Route 9 := (fun mask => (mask,id))

def c1576 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1576 : Upper (D 0) (R 0) [50,320,80,132,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132,1] 13 (by decide) (choices 1) [1,8,128] r1576 c1576
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u493
  · exact u494
  · exact u495

def b1577 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 322 84 140 24 161 225 161 417), lower := (rows 51 322 84 140 24 32 64 128 256), losses := [] }

theorem u1577 : Upper (D 0) (R 0) [50,320,80,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1577
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 84 140 48 169 201 137 393), lower := (rows 51 322 84 140 48 32 64 128 256), losses := [] }

theorem u1578 : Upper (D 0) (R 0) [50,320,80,132,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1578
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1579 : Route 9 := (fun mask => (mask,id))

def c1579 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1579 : Upper (D 0) (R 0) [50,320,80,132,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,132,128] 13 (by decide) (choices 1) [1,8] r1579 c1579
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u496
  · exact u497

def r1580 : Route 9 := (fun mask => (mask,id))

def c1580 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1580 : Upper (D 0) (R 0) [50,320,80,160,1] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160,1] 13 (by decide) (choices 1) [1,4,8,128] r1580 c1580
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u498
  · exact u499
  · exact u500
  · exact u501

def b1581 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 51 322 84 168 20 169 201 137 393), lower := (rows 51 322 84 168 20 32 64 128 256), losses := [] }

theorem u1581 : Upper (D 0) (R 0) [50,320,80,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1581
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 322 84 168 24 165 197 133 389), lower := (rows 51 322 84 168 24 32 64 128 256), losses := [] }

theorem u1582 : Upper (D 0) (R 0) [50,320,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1582
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1583 : Route 9 := (fun mask => (mask,id))

def c1583 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1583 : Upper (D 0) (R 0) [50,320,80,160,128] 13 := by
  apply FastRouting.sound _ _ [50,320,80,160,128] 13 (by decide) (choices 1) [1,4,8] r1583 c1583
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u502
  · exact u503
  · exact u504

def b1584 : PairBound 9 := { available := 108, camps := [{ cop := 2, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 51 322 133 152 17 108 108 236 364), lower := (rows 51 322 133 152 17 32 64 128 256), losses := [] }

theorem u1584 : Upper (D 0) (R 0) [50,320,129,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1584
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 51 322 133 152 20 105 105 233 361), lower := (rows 51 322 133 152 20 32 64 128 256), losses := [] }

theorem u1585 : Upper (D 0) (R 0) [50,320,129,144,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1585
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 101, camps := [], pairs := [], upper := (rows 51 322 133 152 24 101 101 229 357), lower := (rows 51 322 133 152 24 32 64 128 256), losses := [] }

theorem u1586 : Upper (D 0) (R 0) [50,320,129,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1586
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 77, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 133 152 48 109 77 205 333), lower := (rows 51 322 133 152 48 32 64 128 256), losses := [] }

theorem u1587 : Upper (D 0) (R 0) [50,320,129,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1587
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 45, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 133 152 80 45 109 173 301), lower := (rows 51 322 133 152 80 32 64 128 256), losses := [] }

theorem u1588 : Upper (D 0) (R 0) [50,320,129,144,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1588
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1589 : Route 9 := (fun mask => (mask,id))

def c1589 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1589 : Upper (D 0) (R 0) [50,320,129,192,1] 13 := by
  apply FastRouting.sound _ _ [50,320,129,192,1] 13 (by decide) (choices 1) [4,8,16] r1589 c1589
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u505
  · exact u506
  · exact u507

def b1590 : PairBound 9 := { available := 57, camps := [], pairs := [], upper := (rows 51 322 133 200 20 57 121 185 313), lower := (rows 51 322 133 200 20 32 64 128 256), losses := [] }

theorem u1590 : Upper (D 0) (R 0) [50,320,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1590
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 53, camps := [], pairs := [], upper := (rows 51 322 133 200 24 53 117 181 309), lower := (rows 51 322 133 200 24 32 64 128 256), losses := [] }

theorem u1591 : Upper (D 0) (R 0) [50,320,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1591
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 133 200 48 61 93 157 285), lower := (rows 51 322 133 200 48 32 64 128 256), losses := [] }

theorem u1592 : Upper (D 0) (R 0) [50,320,129,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1592
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1593 : Route 9 := (fun mask => (mask,id))

def c1593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1593 : Upper (D 0) (R 0) [50,320,144,160,1] 13 := by
  apply FastRouting.sound _ _ [50,320,144,160,1] 13 (by decide) (choices 1) [1,4,8,64] r1593 c1593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u508
  · exact u509
  · exact u510
  · exact u511

def b1594 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 51 322 148 168 20 105 73 201 329), lower := (rows 51 322 148 168 20 32 64 128 256), losses := [] }

theorem u1594 : Upper (D 0) (R 0) [50,320,144,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1594
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 69, camps := [], pairs := [], upper := (rows 51 322 148 168 24 101 69 197 325), lower := (rows 51 322 148 168 24 32 64 128 256), losses := [] }

theorem u1595 : Upper (D 0) (R 0) [50,320,144,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1595
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 140, targets := 64 }], pairs := [(2,6)], upper := (rows 51 322 148 168 80 45 77 141 269), lower := (rows 51 322 148 168 80 32 64 128 256), losses := [] }

theorem u1596 : Upper (D 0) (R 0) [50,320,144,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1596
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1597 : Route 9 := (fun mask => (mask,id))

def c1597 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1597 : Upper (D 0) (R 0) [50,320,144,192,1] 13 := by
  apply FastRouting.sound _ _ [50,320,144,192,1] 13 (by decide) (choices 1) [1,4,8] r1597 c1597
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u512
  · exact u513
  · exact u514

def b1598 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 322 148 200 20 41 105 169 297), lower := (rows 51 322 148 200 20 32 64 128 256), losses := [] }

theorem u1598 : Upper (D 0) (R 0) [50,320,144,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1598
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 322 148 200 24 37 101 165 293), lower := (rows 51 322 148 200 24 32 64 128 256), losses := [] }

theorem u1599 : Upper (D 0) (R 0) [50,320,144,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1599
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 322 148 200 48 45 77 141 269), lower := (rows 51 322 148 200 48 32 64 128 256), losses := [] }

theorem u1600 : Upper (D 0) (R 0) [50,320,144,192,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1600
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 480, camps := [{ cop := 0, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 14 152 17 480 480 480 480), lower := (rows 113 7 14 152 17 32 64 128 256), losses := [] }

theorem u1601 : Upper (D 0) (R 0) [112,5,10,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1601
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 449, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 152 48 481 449 449 449), lower := (rows 113 7 14 152 48 32 64 128 256), losses := [] }

theorem u1602 : Upper (D 0) (R 0) [112,5,10,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1602
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 353, camps := [{ cop := 3, region := 353, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 14 152 144 353 353 481 353), lower := (rows 113 7 14 152 144 32 64 128 256), losses := [] }

theorem u1603 : Upper (D 0) (R 0) [112,5,10,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1603
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 14 152 272 225 225 225 481), lower := (rows 113 7 14 152 272 32 64 128 256), losses := [] }

theorem u1604 : Upper (D 0) (R 0) [112,5,10,144,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1604
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 14 280 17 224 224 224 480), lower := (rows 113 7 14 280 17 32 64 128 256), losses := [] }

theorem u1605 : Upper (D 0) (R 0) [112,5,10,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1605
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 280 48 225 193 193 449), lower := (rows 113 7 14 280 48 32 64 128 256), losses := [] }

theorem u1606 : Upper (D 0) (R 0) [112,5,10,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1606
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1607 : Route 9 := (fun mask => (mask,id))

def c1607 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1607 : Upper (D 0) (R 0) [112,5,10,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,10,272,128] 13 (by decide) (choices 1) [1,64,128] r1607 c1607
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u515
  · exact u516
  · exact u517

def b1608 : PairBound 9 := { available := 240, camps := [{ cop := 0, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 14 392 17 240 240 240 496), lower := (rows 113 7 14 392 17 32 64 128 256), losses := [] }

theorem u1608 : Upper (D 0) (R 0) [112,5,10,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1608
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 14 392 48 241 209 209 465), lower := (rows 113 7 14 392 48 32 64 128 256), losses := [] }

theorem u1609 : Upper (D 0) (R 0) [112,5,10,384,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1609
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 14 392 144 113 113 241 369), lower := (rows 113 7 14 392 144 32 64 128 256), losses := [] }

theorem u1610 : Upper (D 0) (R 0) [112,5,10,384,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1610
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 113 7 134 265 24 240 240 240 496), lower := (rows 113 7 134 265 24 32 64 128 256), losses := [] }

theorem u1611 : Upper (D 0) (R 0) [112,5,130,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1611
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 134 265 48 248 216 216 472), lower := (rows 113 7 134 265 48 32 64 128 256), losses := [] }

theorem u1612 : Upper (D 0) (R 0) [112,5,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1612
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 120, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 134 265 144 120 120 248 376), lower := (rows 113 7 134 265 144 32 64 128 256), losses := [] }

theorem u1613 : Upper (D 0) (R 0) [112,5,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1613
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 392, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 134 280 17 232 232 232 488), lower := (rows 113 7 134 280 17 32 64 128 256), losses := [] }

theorem u1614 : Upper (D 0) (R 0) [112,5,130,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1614
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 134 280 24 225 225 225 481), lower := (rows 113 7 134 280 24 32 64 128 256), losses := [] }

theorem u1615 : Upper (D 0) (R 0) [112,5,130,272,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1615
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 134 280 48 233 201 201 457), lower := (rows 113 7 134 280 48 32 64 128 256), losses := [] }

theorem u1616 : Upper (D 0) (R 0) [112,5,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1616
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 105, camps := [{ cop := 4, region := 361, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 134 280 144 105 105 233 361), lower := (rows 113 7 134 280 144 32 64 128 256), losses := [] }

theorem u1617 : Upper (D 0) (R 0) [112,5,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1617
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 113 7 140 265 18 240 240 240 496), lower := (rows 113 7 140 265 18 32 64 128 256), losses := [] }

theorem u1618 : Upper (D 0) (R 0) [112,5,136,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1618
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 265 48 242 210 210 466), lower := (rows 113 7 140 265 48 32 64 128 256), losses := [] }

theorem u1619 : Upper (D 0) (R 0) [112,5,136,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1619
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P00
