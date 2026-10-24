import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0008
import IrregularNine14P00C0009

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m1620_2 : Upper (D 0) (R 0) [112,5,136,257,128,2] 13 :=
  permutation_upper _ _ _ [112,5,136,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u518

theorem m1620_16 : Upper (D 0) (R 0) [112,5,136,257,128,16] 13 :=
  permutation_upper _ _ _ [112,5,136,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u519

theorem m1620_64 : Upper (D 0) (R 0) [112,5,136,257,128,64] 13 :=
  permutation_upper _ _ _ [112,5,136,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u520

def r1620 : Route 9 := (fun mask => (mask,id))

def c1620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1620 : Upper (D 0) (R 0) [112,5,136,257,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,257,128] 13 (by decide) (choices 1) [2,16,64] r1620 c1620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1620_2
  · exact m1620_16
  · exact m1620_64

def b1621 : PairBound 9 := { available := 240, camps := [], pairs := [(2,0)], upper := (rows 113 7 140 266 17 240 240 240 496), lower := (rows 113 7 140 266 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 49 81 145 273), good := (rows 496 494 140 270 496 32 64 128 256) }] }

theorem u1621 : Upper (D 0) (R 0) [112,5,136,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1621
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 266 48 241 209 209 465), lower := (rows 113 7 140 266 48 32 64 128 256), losses := [] }

theorem u1622 : Upper (D 0) (R 0) [112,5,136,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1622
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 140 266 144 113 113 241 369), lower := (rows 113 7 140 266 144 32 64 128 256), losses := [] }

theorem u1623 : Upper (D 0) (R 0) [112,5,136,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1623
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1624 : Route 9 := (fun mask => (mask,id))

def c1624 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1624 : Upper (D 0) (R 0) [112,5,136,272,1] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,1] 13 (by decide) (choices 1) [2,64,128] r1624 c1624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u521
  · exact u522
  · exact u523

def b1625 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 140 280 18 225 225 225 481), lower := (rows 113 7 140 280 18 32 64 128 256), losses := [] }

theorem u1625 : Upper (D 0) (R 0) [112,5,136,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1625
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 140 280 48 227 195 195 451), lower := (rows 113 7 140 280 48 32 64 128 256), losses := [] }

theorem u1626 : Upper (D 0) (R 0) [112,5,136,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1626
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1627 : Route 9 := (fun mask => (mask,id))

def c1627 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1627 : Upper (D 0) (R 0) [112,5,136,272,128] 13 := by
  apply FastRouting.sound _ _ [112,5,136,272,128] 13 (by decide) (choices 1) [1,2,64] r1627 c1627
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u524
  · exact u525
  · exact u526

def b1628 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 113 7 262 137 24 240 240 240 496), lower := (rows 113 7 262 137 24 32 64 128 256), losses := [] }

theorem u1628 : Upper (D 0) (R 0) [112,5,258,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1628
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 216, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 262 137 48 248 216 216 472), lower := (rows 113 7 262 137 48 32 64 128 256), losses := [] }

theorem u1629 : Upper (D 0) (R 0) [112,5,258,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1629
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1630_8 : Upper (D 0) (R 0) [112,5,258,129,128,8] 13 :=
  permutation_upper _ _ _ [112,5,258,129,8,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u527

theorem m1630_16 : Upper (D 0) (R 0) [112,5,258,129,128,16] 13 :=
  permutation_upper _ _ _ [112,5,258,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u528

theorem m1630_64 : Upper (D 0) (R 0) [112,5,258,129,128,64] 13 :=
  permutation_upper _ _ _ [112,5,258,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u529

def r1630 : Route 9 := (fun mask => (mask,id))

def c1630 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1630 : Upper (D 0) (R 0) [112,5,258,129,128] 13 := by
  apply FastRouting.sound _ _ [112,5,258,129,128] 13 (by decide) (choices 1) [8,16,64] r1630 c1630
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1630_8
  · exact m1630_16
  · exact m1630_64

def b1631 : PairBound 9 := { available := 232, camps := [{ cop := 0, region := 136, targets := 1 }], pairs := [(3,0)], upper := (rows 113 7 262 152 17 232 232 232 488), lower := (rows 113 7 262 152 17 32 64 128 256), losses := [] }

theorem u1631 : Upper (D 0) (R 0) [112,5,258,144,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1631
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 262 152 24 225 225 225 481), lower := (rows 113 7 262 152 24 32 64 128 256), losses := [] }

theorem u1632 : Upper (D 0) (R 0) [112,5,258,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1632
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 262 152 48 233 201 201 457), lower := (rows 113 7 262 152 48 32 64 128 256), losses := [] }

theorem u1633 : Upper (D 0) (R 0) [112,5,258,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1633
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 262 152 144 105 105 233 361), lower := (rows 113 7 262 152 144 32 64 128 256), losses := [] }

theorem u1634 : Upper (D 0) (R 0) [112,5,258,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1634
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 113 7 268 137 18 240 240 240 496), lower := (rows 113 7 268 137 18 32 64 128 256), losses := [] }

theorem u1635 : Upper (D 0) (R 0) [112,5,264,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1635
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 137 48 242 210 210 466), lower := (rows 113 7 268 137 48 32 64 128 256), losses := [] }

theorem u1636 : Upper (D 0) (R 0) [112,5,264,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1636
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1637_2 : Upper (D 0) (R 0) [112,5,264,129,128,2] 13 :=
  permutation_upper _ _ _ [112,5,264,129,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u530

theorem m1637_16 : Upper (D 0) (R 0) [112,5,264,129,128,16] 13 :=
  permutation_upper _ _ _ [112,5,264,129,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u531

theorem m1637_64 : Upper (D 0) (R 0) [112,5,264,129,128,64] 13 :=
  permutation_upper _ _ _ [112,5,264,129,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u532

def r1637 : Route 9 := (fun mask => (mask,id))

def c1637 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1637 : Upper (D 0) (R 0) [112,5,264,129,128] 13 := by
  apply FastRouting.sound _ _ [112,5,264,129,128] 13 (by decide) (choices 1) [2,16,64] r1637 c1637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1637_2
  · exact m1637_16
  · exact m1637_64

def b1638 : PairBound 9 := { available := 240, camps := [], pairs := [(2,0)], upper := (rows 113 7 268 138 17 240 240 240 496), lower := (rows 113 7 268 138 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 2 6 10 16 49 81 145 273), good := (rows 496 494 268 142 496 32 64 128 256) }] }

theorem u1638 : Upper (D 0) (R 0) [112,5,264,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1638
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 138 48 241 209 209 465), lower := (rows 113 7 268 138 48 32 64 128 256), losses := [] }

theorem u1639 : Upper (D 0) (R 0) [112,5,264,130,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1639
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 268 138 144 113 113 241 369), lower := (rows 113 7 268 138 144 32 64 128 256), losses := [] }

theorem u1640 : Upper (D 0) (R 0) [112,5,264,130,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1640
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1641 : Route 9 := (fun mask => (mask,id))

def c1641 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1641 : Upper (D 0) (R 0) [112,5,264,144,1] 13 := by
  apply FastRouting.sound _ _ [112,5,264,144,1] 13 (by decide) (choices 1) [2,64,128] r1641 c1641
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b1642 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 268 152 18 225 225 225 481), lower := (rows 113 7 268 152 18 32 64 128 256), losses := [] }

theorem u1642 : Upper (D 0) (R 0) [112,5,264,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1642
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 268 152 48 227 195 195 451), lower := (rows 113 7 268 152 48 32 64 128 256), losses := [] }

theorem u1643 : Upper (D 0) (R 0) [112,5,264,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1643
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 99, camps := [{ cop := 3, region := 359, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 268 152 144 99 99 227 355), lower := (rows 113 7 268 152 144 32 64 128 256), losses := [] }

theorem u1644 : Upper (D 0) (R 0) [112,5,264,144,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1644
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 232, camps := [{ cop := 1, region := 24, targets := 32 }], pairs := [(3,5)], upper := (rows 113 7 388 26 17 232 232 232 488), lower := (rows 113 7 388 26 17 32 64 128 256), losses := [] }

theorem u1645 : Upper (D 0) (R 0) [112,5,384,18,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1645
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 7 388 26 24 225 225 225 481), lower := (rows 113 7 388 26 24 32 64 128 256), losses := [] }

theorem u1646 : Upper (D 0) (R 0) [112,5,384,18,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1646
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 201, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 388 26 48 233 201 201 457), lower := (rows 113 7 388 26 48 32 64 128 256), losses := [] }

theorem u1647 : Upper (D 0) (R 0) [112,5,384,18,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1647
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 105, camps := [{ cop := 3, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 7 388 26 144 105 105 233 361), lower := (rows 113 7 388 26 144 32 64 128 256), losses := [] }

theorem u1648 : Upper (D 0) (R 0) [112,5,384,18,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1648
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 120, camps := [], pairs := [], upper := (rows 113 7 388 137 18 120 120 248 376), lower := (rows 113 7 388 137 18 32 64 128 256), losses := [] }

theorem u1649 : Upper (D 0) (R 0) [112,5,384,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1649
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 114, camps := [], pairs := [], upper := (rows 113 7 388 137 24 114 114 242 370), lower := (rows 113 7 388 137 24 32 64 128 256), losses := [] }

theorem u1650 : Upper (D 0) (R 0) [112,5,384,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1650
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 90, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 388 137 48 122 90 218 346), lower := (rows 113 7 388 137 48 32 64 128 256), losses := [] }

theorem u1651 : Upper (D 0) (R 0) [112,5,384,129,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1651
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1652 : Route 9 := (fun mask => (mask,id))

def c1652 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1652 : Upper (D 0) (R 0) [112,5,384,144,1] 13 := by
  apply FastRouting.sound _ _ [112,5,384,144,1] 13 (by decide) (choices 1) [2,8,64] r1652 c1652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u536
  · exact u537
  · exact u538

def b1653 : PairBound 9 := { available := 105, camps := [], pairs := [], upper := (rows 113 7 388 152 18 105 105 233 361), lower := (rows 113 7 388 152 18 32 64 128 256), losses := [] }

theorem u1653 : Upper (D 0) (R 0) [112,5,384,144,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1653
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 99, camps := [], pairs := [], upper := (rows 113 7 388 152 24 99 99 227 355), lower := (rows 113 7 388 152 24 32 64 128 256), losses := [] }

theorem u1654 : Upper (D 0) (R 0) [112,5,384,144,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1654
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 75, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 7 388 152 48 107 75 203 331), lower := (rows 113 7 388 152 48 32 64 128 256), losses := [] }

theorem u1655 : Upper (D 0) (R 0) [112,5,384,144,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1655
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 240, camps := [], pairs := [], upper := (rows 113 14 133 265 18 240 240 240 496), lower := (rows 113 14 133 265 18 32 64 128 256), losses := [] }

theorem u1656 : Upper (D 0) (R 0) [112,12,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1656
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 210, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 265 48 242 210 210 466), lower := (rows 113 14 133 265 48 32 64 128 256), losses := [] }

theorem u1657 : Upper (D 0) (R 0) [112,12,129,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1657
    (constants 0).1 (constants 0).2 (by decide +kernel)

theorem m1658_2 : Upper (D 0) (R 0) [112,12,129,257,128,2] 13 :=
  permutation_upper _ _ _ [112,12,129,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u539

theorem m1658_16 : Upper (D 0) (R 0) [112,12,129,257,128,16] 13 :=
  permutation_upper _ _ _ [112,12,129,257,32,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u540

theorem m1658_64 : Upper (D 0) (R 0) [112,12,129,257,128,64] 13 :=
  permutation_upper _ _ _ [112,12,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 5 | 5 => 4 | 6 => 6 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u541

def r1658 : Route 9 := (fun mask => (mask,id))

def c1658 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1658 : Upper (D 0) (R 0) [112,12,129,257,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,257,128] 13 (by decide) (choices 1) [2,16,64] r1658 c1658
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact m1658_2
  · exact m1658_16
  · exact m1658_64

def b1659 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 113 14 133 266 17 240 240 240 496), lower := (rows 113 14 133 266 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 6 4 12 16 49 81 145 273), good := (rows 496 14 494 266 496 32 64 128 256) }] }

theorem u1659 : Upper (D 0) (R 0) [112,12,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1659
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 266 48 241 209 209 465), lower := (rows 113 14 133 266 48 32 64 128 256), losses := [] }

theorem u1660 : Upper (D 0) (R 0) [112,12,129,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1660
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 133 266 144 113 113 241 369), lower := (rows 113 14 133 266 144 32 64 128 256), losses := [] }

theorem u1661 : Upper (D 0) (R 0) [112,12,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1661
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1662 : Route 9 := (fun mask => (mask,id))

def c1662 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1662 : Upper (D 0) (R 0) [112,12,129,272,1] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,1] 13 (by decide) (choices 1) [2,64,128] r1662 c1662
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u542
  · exact u543
  · exact u544

def b1663 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 14 133 280 18 225 225 225 481), lower := (rows 113 14 133 280 18 32 64 128 256), losses := [] }

theorem u1663 : Upper (D 0) (R 0) [112,12,129,272,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1663
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 133 280 48 227 195 195 451), lower := (rows 113 14 133 280 48 32 64 128 256), losses := [] }

theorem u1664 : Upper (D 0) (R 0) [112,12,129,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1664
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1665 : Route 9 := (fun mask => (mask,id))

def c1665 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1665 : Upper (D 0) (R 0) [112,12,129,272,128] 13 := by
  apply FastRouting.sound _ _ [112,12,129,272,128] 13 (by decide) (choices 1) [1,2,64] r1665 c1665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u545
  · exact u546
  · exact u547

def b1666 : PairBound 9 := { available := 240, camps := [], pairs := [(1,0)], upper := (rows 113 14 134 265 17 240 240 240 496), lower := (rows 113 14 134 265 17 32 64 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 49 81 145 273), good := (rows 496 14 134 494 496 32 64 128 256) }] }

theorem u1666 : Upper (D 0) (R 0) [112,12,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1666
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 209, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 134 265 48 241 209 209 465), lower := (rows 113 14 134 265 48 32 64 128 256), losses := [] }

theorem u1667 : Upper (D 0) (R 0) [112,12,130,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1667
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 113, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 134 265 144 113 113 241 369), lower := (rows 113 14 134 265 144 32 64 128 256), losses := [] }

theorem u1668 : Upper (D 0) (R 0) [112,12,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1668
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 113 14 134 280 17 225 225 225 481), lower := (rows 113 14 134 280 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 10 12 8 0 49 81 145 273), good := (rows 481 14 134 494 481 32 64 128 256) }] }

theorem u1669 : Upper (D 0) (R 0) [112,12,130,272,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1669
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 134 280 48 225 193 193 449), lower := (rows 113 14 134 280 48 32 64 128 256), losses := [] }

theorem u1670 : Upper (D 0) (R 0) [112,12,130,272,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1670
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 134 280 144 97 97 225 353), lower := (rows 113 14 134 280 144 32 64 128 256), losses := [] }

theorem u1671 : Upper (D 0) (R 0) [112,12,130,272,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1671
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1672 : Route 9 := (fun mask => (mask,id))

def c1672 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1672 : Upper (D 0) (R 0) [112,12,144,257,1] 13 := by
  apply FastRouting.sound _ _ [112,12,144,257,1] 13 (by decide) (choices 1) [2,64,128] r1672 c1672
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u548
  · exact u549
  · exact u550

def b1673 : PairBound 9 := { available := 225, camps := [], pairs := [], upper := (rows 113 14 148 265 18 225 225 225 481), lower := (rows 113 14 148 265 18 32 64 128 256), losses := [] }

theorem u1673 : Upper (D 0) (R 0) [112,12,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1673
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 195, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 265 48 227 195 195 451), lower := (rows 113 14 148 265 48 32 64 128 256), losses := [] }

theorem u1674 : Upper (D 0) (R 0) [112,12,144,257,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1674
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 99, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 265 144 99 99 227 355), lower := (rows 113 14 148 265 144 32 64 128 256), losses := [] }

theorem u1675 : Upper (D 0) (R 0) [112,12,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1675
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 225, camps := [], pairs := [(1,4)], upper := (rows 113 14 148 266 17 225 225 225 481), lower := (rows 113 14 148 266 17 32 64 128 256), losses := [{ target := 4, region := (rows 1 6 4 12 0 49 81 145 273), good := (rows 481 14 494 266 481 32 64 128 256) }] }

theorem u1676 : Upper (D 0) (R 0) [112,12,144,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1676
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 14 148 266 48 225 193 193 449), lower := (rows 113 14 148 266 48 32 64 128 256), losses := [] }

theorem u1677 : Upper (D 0) (R 0) [112,12,144,258,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1677
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 97, targets := 128 }], pairs := [(0,7)], upper := (rows 113 14 148 266 144 97 97 225 353), lower := (rows 113 14 148 266 144 32 64 128 256), losses := [] }

theorem u1678 : Upper (D 0) (R 0) [112,12,144,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b1678
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r1679 : Route 9 := (fun mask => (mask,id))

def c1679 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1679 : Upper (D 0) (R 0) [112,12,144,288,1] 13 := by
  apply FastRouting.sound _ _ [112,12,144,288,1] 13 (by decide) (choices 1) [1,2,64,128] r1679 c1679
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u551
  · exact u552
  · exact u553
  · exact u554

#print axioms u1679
end Delivery.IrregularNine14.P00
