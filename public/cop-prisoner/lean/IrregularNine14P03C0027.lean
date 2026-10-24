import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem m1620_2 : Upper (D 3) (R 3) [96,5,24,129,257,128,2] 13 :=
  permutation_upper _ _ _ [96,5,24,129,257,2,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u275

theorem m1620_32 : Upper (D 3) (R 3) [96,5,24,129,257,128,32] 13 :=
  permutation_upper _ _ _ [96,5,24,129,257,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u276

def r1620 : Route 9 := (fun mask => (mask,id))

def c1620 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1620 : Upper (D 3) (R 3) [96,5,24,129,257,128] 13 := by
  apply FastRouting.sound _ _ [96,5,24,129,257,128] 13 (by decide) (choices 1) [2,32] r1620 c1620
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1620_2
  · exact m1620_32

def b1621 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 274 33 224 224 480), lower := (rows 97 7 28 137 274 33 64 128 256), losses := [] }

theorem u1621 : Upper (D 3) (R 3) [96,5,24,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1621
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 137 274 96 225 161 417), lower := (rows 97 7 28 137 274 96 64 128 256), losses := [] }

theorem u1622 : Upper (D 3) (R 3) [96,5,24,129,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1622
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 137 274 160 97 225 353), lower := (rows 97 7 28 137 274 160 64 128 256), losses := [] }

theorem u1623 : Upper (D 3) (R 3) [96,5,24,129,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1623
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1624 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 273 33 224 224 480), lower := (rows 97 7 28 138 273 33 64 128 256), losses := [] }

theorem u1624 : Upper (D 3) (R 3) [96,5,24,130,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1624
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 138 273 96 225 161 417), lower := (rows 97 7 28 138 273 96 64 128 256), losses := [] }

theorem u1625 : Upper (D 3) (R 3) [96,5,24,130,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1625
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 28 138 273 160 97 225 353), lower := (rows 97 7 28 138 273 160 64 128 256), losses := [] }

theorem u1626 : Upper (D 3) (R 3) [96,5,24,130,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1626
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 280 33 224 224 480), lower := (rows 97 7 134 25 280 33 64 128 256), losses := [] }

theorem u1627 : Upper (D 3) (R 3) [96,5,130,17,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1627
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 134, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 25 280 96 225 161 417), lower := (rows 97 7 134 25 280 96 64 128 256), losses := [] }

theorem u1628 : Upper (D 3) (R 3) [96,5,130,17,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1628
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 25 280 160 97 225 353), lower := (rows 97 7 134 25 280 160 64 128 256), losses := [] }

theorem u1629 : Upper (D 3) (R 3) [96,5,130,17,264,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1629
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 134 56 273 33 200 200 456), lower := (rows 97 7 134 56 273 33 64 128 256), losses := [] }

theorem u1630 : Upper (D 3) (R 3) [96,5,130,48,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1630
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 134 56 273 40 193 193 449), lower := (rows 97 7 134 56 273 40 64 128 256), losses := [] }

theorem u1631 : Upper (D 3) (R 3) [96,5,130,48,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1631
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 134 56 273 96 201 137 393), lower := (rows 97 7 134 56 273 96 64 128 256), losses := [] }

theorem u1632 : Upper (D 3) (R 3) [96,5,130,48,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1632
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 73, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 273 160 73 201 329), lower := (rows 97 7 134 56 273 160 64 128 256), losses := [] }

theorem u1633 : Upper (D 3) (R 3) [96,5,130,48,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1633
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 336 33 201 137 393), lower := (rows 97 7 134 56 336 33 64 128 256), losses := [] }

theorem u1634 : Upper (D 3) (R 3) [96,5,130,48,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1634
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 134 56 336 40 193 129 385), lower := (rows 97 7 134 56 336 40 64 128 256), losses := [] }

theorem u1635 : Upper (D 3) (R 3) [96,5,130,48,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1635
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 345, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 134 56 336 160 73 137 265), lower := (rows 97 7 134 56 336 160 64 128 256), losses := [] }

theorem u1636 : Upper (D 3) (R 3) [96,5,130,48,320,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1636
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 274 33 224 224 480), lower := (rows 97 7 140 25 274 33 64 128 256), losses := [] }

theorem u1637 : Upper (D 3) (R 3) [96,5,136,17,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1637
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 25 274 96 225 161 417), lower := (rows 97 7 140 25 274 96 64 128 256), losses := [] }

theorem u1638 : Upper (D 3) (R 3) [96,5,136,17,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1638
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 25 274 160 97 225 353), lower := (rows 97 7 140 25 274 160 64 128 256), losses := [] }

theorem u1639 : Upper (D 3) (R 3) [96,5,136,17,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1639
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 273 33 224 224 480), lower := (rows 97 7 140 26 273 33 64 128 256), losses := [] }

theorem u1640 : Upper (D 3) (R 3) [96,5,136,18,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1640
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 26 273 96 225 161 417), lower := (rows 97 7 140 26 273 96 64 128 256), losses := [] }

theorem u1641 : Upper (D 3) (R 3) [96,5,136,18,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1641
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 26 273 160 97 225 353), lower := (rows 97 7 140 26 273 160 64 128 256), losses := [] }

theorem u1642 : Upper (D 3) (R 3) [96,5,136,18,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1642
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 140 265 50 33 208 208 464), lower := (rows 97 7 140 265 50 33 64 128 256), losses := [] }

theorem u1643 : Upper (D 3) (R 3) [96,5,136,257,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1643
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 140 265 50 48 193 193 449), lower := (rows 97 7 140 265 50 48 64 128 256), losses := [] }

theorem u1644 : Upper (D 3) (R 3) [96,5,136,257,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1644
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 265 50 96 209 145 401), lower := (rows 97 7 140 265 50 96 64 128 256), losses := [] }

theorem u1645 : Upper (D 3) (R 3) [96,5,136,257,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1645
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 265 50 160 81 209 337), lower := (rows 97 7 140 265 50 160 64 128 256), losses := [] }

theorem u1646 : Upper (D 3) (R 3) [96,5,136,257,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1646
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 97 7 140 265 145 34 112 240 368), lower := (rows 97 7 140 265 145 34 64 128 256), losses := [] }

theorem u1647 : Upper (D 3) (R 3) [96,5,136,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1647
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 98, camps := [], pairs := [], upper := (rows 97 7 140 265 145 48 98 226 354), lower := (rows 97 7 140 265 145 48 64 128 256), losses := [] }

theorem u1648 : Upper (D 3) (R 3) [96,5,136,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1648
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 265 145 96 114 178 306), lower := (rows 97 7 140 265 145 96 64 128 256), losses := [] }

theorem u1649 : Upper (D 3) (R 3) [96,5,136,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1649
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 140 265 176 33 82 210 338), lower := (rows 97 7 140 265 176 33 64 128 256), losses := [] }

theorem u1650 : Upper (D 3) (R 3) [96,5,136,257,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1650
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 140 265 176 34 81 209 337), lower := (rows 97 7 140 265 176 34 64 128 256), losses := [] }

theorem u1651 : Upper (D 3) (R 3) [96,5,136,257,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1651
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 140 265 176 48 67 195 323), lower := (rows 97 7 140 265 176 48 64 128 256), losses := [] }

theorem u1652 : Upper (D 3) (R 3) [96,5,136,257,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1652
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 140 265 176 96 83 147 275), lower := (rows 97 7 140 265 176 96 64 128 256), losses := [] }

theorem u1653 : Upper (D 3) (R 3) [96,5,136,257,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1653
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 200, camps := [{ cop := 4, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 262 56 145 33 200 200 456), lower := (rows 97 7 262 56 145 33 64 128 256), losses := [] }

theorem u1654 : Upper (D 3) (R 3) [96,5,258,48,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1654
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 262 56 145 40 193 193 449), lower := (rows 97 7 262 56 145 40 64 128 256), losses := [] }

theorem u1655 : Upper (D 3) (R 3) [96,5,258,48,129,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1655
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 137, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 56 145 96 201 137 393), lower := (rows 97 7 262 56 145 96 64 128 256), losses := [] }

theorem u1656 : Upper (D 3) (R 3) [96,5,258,48,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1656
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 73, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 56 145 160 73 201 329), lower := (rows 97 7 262 56 145 160 64 128 256), losses := [] }

theorem u1657 : Upper (D 3) (R 3) [96,5,258,48,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1657
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 137, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 56 208 33 201 137 393), lower := (rows 97 7 262 56 208 33 64 128 256), losses := [] }

theorem u1658 : Upper (D 3) (R 3) [96,5,258,48,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1658
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 7 262 56 208 40 193 129 385), lower := (rows 97 7 262 56 208 40 64 128 256), losses := [] }

theorem u1659 : Upper (D 3) (R 3) [96,5,258,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1659
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 56 208 160 73 137 265), lower := (rows 97 7 262 56 208 160 64 128 256), losses := [] }

theorem u1660 : Upper (D 3) (R 3) [96,5,258,48,192,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1660
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 262 137 176 33 88 216 344), lower := (rows 97 7 262 137 176 33 64 128 256), losses := [] }

theorem u1661 : Upper (D 3) (R 3) [96,5,258,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1661
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 262 137 176 40 81 209 337), lower := (rows 97 7 262 137 176 40 64 128 256), losses := [] }

theorem u1662 : Upper (D 3) (R 3) [96,5,258,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1662
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 7 262 137 176 48 73 201 329), lower := (rows 97 7 262 137 176 48 64 128 256), losses := [] }

theorem u1663 : Upper (D 3) (R 3) [96,5,258,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1663
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 262 137 176 96 89 153 281), lower := (rows 97 7 262 137 176 96 64 128 256), losses := [] }

theorem u1664 : Upper (D 3) (R 3) [96,5,258,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1664
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1665 : PairBound 9 := { available := 25, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 262 168 208 33 89 153 281), lower := (rows 97 7 262 168 208 33 64 128 256), losses := [] }

theorem u1665 : Upper (D 3) (R 3) [96,5,258,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1665
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 7 262 168 208 40 81 145 273), lower := (rows 97 7 262 168 208 40 64 128 256), losses := [] }

theorem u1666 : Upper (D 3) (R 3) [96,5,258,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1666
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 7 262 168 208 48 73 137 265), lower := (rows 97 7 262 168 208 48 64 128 256), losses := [] }

theorem u1667 : Upper (D 3) (R 3) [96,5,258,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1667
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 26 145 33 224 224 480), lower := (rows 97 7 268 26 145 33 64 128 256), losses := [] }

theorem u1668 : Upper (D 3) (R 3) [96,5,264,18,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1668
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 26 145 96 225 161 417), lower := (rows 97 7 268 26 145 96 64 128 256), losses := [] }

theorem u1669 : Upper (D 3) (R 3) [96,5,264,18,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1669
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 26 145 160 97 225 353), lower := (rows 97 7 268 26 145 160 64 128 256), losses := [] }

theorem u1670 : Upper (D 3) (R 3) [96,5,264,18,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1670
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 208, camps := [{ cop := 1, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 137 50 33 208 208 464), lower := (rows 97 7 268 137 50 33 64 128 256), losses := [] }

theorem u1671 : Upper (D 3) (R 3) [96,5,264,129,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1671
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 97 7 268 137 50 48 193 193 449), lower := (rows 97 7 268 137 50 48 64 128 256), losses := [] }

theorem u1672 : Upper (D 3) (R 3) [96,5,264,129,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1672
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 137 50 96 209 145 401), lower := (rows 97 7 268 137 50 96 64 128 256), losses := [] }

theorem u1673 : Upper (D 3) (R 3) [96,5,264,129,34,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1673
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 268 137 50 160 81 209 337), lower := (rows 97 7 268 137 50 160 64 128 256), losses := [] }

theorem u1674 : Upper (D 3) (R 3) [96,5,264,129,34,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1674
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 97 7 268 137 176 33 82 210 338), lower := (rows 97 7 268 137 176 33 64 128 256), losses := [] }

theorem u1675 : Upper (D 3) (R 3) [96,5,264,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1675
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 7 268 137 176 34 81 209 337), lower := (rows 97 7 268 137 176 34 64 128 256), losses := [] }

theorem u1676 : Upper (D 3) (R 3) [96,5,264,129,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1676
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 7 268 137 176 48 67 195 323), lower := (rows 97 7 268 137 176 48 64 128 256), losses := [] }

theorem u1677 : Upper (D 3) (R 3) [96,5,264,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1677
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 268 137 176 96 83 147 275), lower := (rows 97 7 268 137 176 96 64 128 256), losses := [] }

theorem u1678 : Upper (D 3) (R 3) [96,5,264,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1678
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 97 7 388 42 88 33 209 145 401), lower := (rows 97 7 388 42 88 33 64 128 256), losses := [] }

theorem u1679 : Upper (D 3) (R 3) [96,5,384,34,72,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1679
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P03
