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

def b1560 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 35 262 69 137 176 40 81 209 337), lower := (rows 35 262 69 137 176 40 64 128 256), losses := [] }

theorem u1560 : Upper (D 3) (R 3) [34,260,65,129,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1560
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 35 262 69 137 176 48 73 201 329), lower := (rows 35 262 69 137 176 48 64 128 256), losses := [] }

theorem u1561 : Upper (D 3) (R 3) [34,260,65,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1561
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 69 137 176 96 89 153 281), lower := (rows 35 262 69 137 176 96 64 128 256), losses := [] }

theorem u1562 : Upper (D 3) (R 3) [34,260,65,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1562
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 137 208 33 120 184 312), lower := (rows 35 262 69 137 208 33 64 128 256), losses := [] }

theorem u1563 : Upper (D 3) (R 3) [34,260,65,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1563
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 262 69 137 208 40 113 177 305), lower := (rows 35 262 69 137 208 40 64 128 256), losses := [] }

theorem u1564 : Upper (D 3) (R 3) [34,260,65,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1564
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 35 262 69 137 208 48 105 169 297), lower := (rows 35 262 69 137 208 48 64 128 256), losses := [] }

theorem u1565 : Upper (D 3) (R 3) [34,260,65,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1565
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 69 168 208 33 89 153 281), lower := (rows 35 262 69 168 208 33 64 128 256), losses := [] }

theorem u1566 : Upper (D 3) (R 3) [34,260,65,160,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1566
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 262 69 168 208 40 81 145 273), lower := (rows 35 262 69 168 208 40 64 128 256), losses := [] }

theorem u1567 : Upper (D 3) (R 3) [34,260,65,160,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1567
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 262 69 168 208 48 73 137 265), lower := (rows 35 262 69 168 208 48 64 128 256), losses := [] }

theorem u1568 : Upper (D 3) (R 3) [34,260,65,160,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1568
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 112 33 209 145 401), lower := (rows 35 262 76 137 112 33 64 128 256), losses := [] }

theorem u1569 : Upper (D 3) (R 3) [34,260,72,129,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1569
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 262 76 137 112 48 193 129 385), lower := (rows 35 262 76 137 112 48 64 128 256), losses := [] }

theorem u1570 : Upper (D 3) (R 3) [34,260,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1570
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 262 76 137 112 160 81 145 273), lower := (rows 35 262 76 137 112 160 64 128 256), losses := [] }

theorem u1571 : Upper (D 3) (R 3) [34,260,72,129,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1571
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 176 33 81 209 337), lower := (rows 35 262 76 137 176 33 64 128 256), losses := [] }

theorem u1572 : Upper (D 3) (R 3) [34,260,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1572
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 262 76 137 176 48 65 193 321), lower := (rows 35 262 76 137 176 48 64 128 256), losses := [] }

theorem u1573 : Upper (D 3) (R 3) [34,260,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1573
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 152, targets := 64 }], pairs := [(3,6)], upper := (rows 35 262 76 137 176 96 81 145 273), lower := (rows 35 262 76 137 176 96 64 128 256), losses := [] }

theorem u1574 : Upper (D 3) (R 3) [34,260,72,129,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1574
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 76 137 208 33 113 177 305), lower := (rows 35 262 76 137 208 33 64 128 256), losses := [] }

theorem u1575 : Upper (D 3) (R 3) [34,260,72,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1575
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 76 137 208 48 97 161 289), lower := (rows 35 262 76 137 208 48 64 128 256), losses := [] }

theorem u1576 : Upper (D 3) (R 3) [34,260,72,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1576
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 262 196 88 176 33 73 137 265), lower := (rows 35 262 196 88 176 33 64 128 256), losses := [] }

theorem u1577 : Upper (D 3) (R 3) [34,260,192,80,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1577
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 262 196 88 176 40 65 129 257), lower := (rows 35 262 196 88 176 40 64 128 256), losses := [] }

theorem u1578 : Upper (D 3) (R 3) [34,260,192,80,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1578
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 112 33 209 145 401), lower := (rows 35 322 13 140 112 33 64 128 256), losses := [] }

theorem u1579 : Upper (D 3) (R 3) [34,320,9,132,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1579
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 13 140 112 48 193 129 385), lower := (rows 35 322 13 140 112 48 64 128 256), losses := [] }

theorem u1580 : Upper (D 3) (R 3) [34,320,9,132,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1580
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 13 140 112 160 81 145 273), lower := (rows 35 322 13 140 112 160 64 128 256), losses := [] }

theorem u1581 : Upper (D 3) (R 3) [34,320,9,132,96,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1581
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 28 104 145 33 197 133 389), lower := (rows 35 322 28 104 145 33 64 128 256), losses := [] }

theorem u1582 : Upper (D 3) (R 3) [34,320,24,96,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1582
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 28 104 145 36 193 129 385), lower := (rows 35 322 28 104 145 36 64 128 256), losses := [] }

theorem u1583 : Upper (D 3) (R 3) [34,320,24,96,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1583
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1584 : Route 9 := (fun mask => (mask,id))

def c1584 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1584 : Upper (D 3) (R 3) [34,320,24,96,129,128] 13 := by
  apply FastRouting.sound _ _ [34,320,24,96,129,128] 13 (by decide) (choices 1) [1,4] r1584 c1584
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u273
  · exact u274

def b1585 : PairBound 9 := { available := 133, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 88 145 33 197 133 389), lower := (rows 35 322 44 88 145 33 64 128 256), losses := [] }

theorem u1585 : Upper (D 3) (R 3) [34,320,40,80,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1585
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 44 88 145 36 193 129 385), lower := (rows 35 322 44 88 145 36 64 128 256), losses := [] }

theorem u1586 : Upper (D 3) (R 3) [34,320,40,80,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1586
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 323, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 88 145 160 69 133 261), lower := (rows 35 322 44 88 145 160 64 128 256), losses := [] }

theorem u1587 : Upper (D 3) (R 3) [34,320,40,80,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1587
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 137 84 33 209 145 401), lower := (rows 35 322 44 137 84 33 64 128 256), losses := [] }

theorem u1588 : Upper (D 3) (R 3) [34,320,40,129,68,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1588
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 322 44 137 84 48 193 129 385), lower := (rows 35 322 44 137 84 48 64 128 256), losses := [] }

theorem u1589 : Upper (D 3) (R 3) [34,320,40,129,68,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1589
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 339, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 44 137 84 160 81 145 273), lower := (rows 35 322 44 137 84 160 64 128 256), losses := [] }

theorem u1590 : Upper (D 3) (R 3) [34,320,40,129,68,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1590
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 137 208 33 85 149 277), lower := (rows 35 322 44 137 208 33 64 128 256), losses := [] }

theorem u1591 : Upper (D 3) (R 3) [34,320,40,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1591
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 44 137 208 36 81 145 273), lower := (rows 35 322 44 137 208 36 64 128 256), losses := [] }

theorem u1592 : Upper (D 3) (R 3) [34,320,40,129,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1592
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 322 44 137 208 48 69 133 261), lower := (rows 35 322 44 137 208 48 64 128 256), losses := [] }

theorem u1593 : Upper (D 3) (R 3) [34,320,40,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1593
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 44 200 145 33 85 149 277), lower := (rows 35 322 44 200 145 33 64 128 256), losses := [] }

theorem u1594 : Upper (D 3) (R 3) [34,320,40,192,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1594
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 44 200 145 36 81 145 273), lower := (rows 35 322 44 200 145 36 64 128 256), losses := [] }

theorem u1595 : Upper (D 3) (R 3) [34,320,40,192,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1595
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 322 44 200 145 48 69 133 261), lower := (rows 35 322 44 200 145 48 64 128 256), losses := [] }

theorem u1596 : Upper (D 3) (R 3) [34,320,40,192,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1596
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 137 176 33 85 149 277), lower := (rows 35 322 76 137 176 33 64 128 256), losses := [] }

theorem u1597 : Upper (D 3) (R 3) [34,320,72,129,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1597
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 76 137 176 36 81 145 273), lower := (rows 35 322 76 137 176 36 64 128 256), losses := [] }

theorem u1598 : Upper (D 3) (R 3) [34,320,72,129,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1598
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 322 76 137 176 48 69 133 261), lower := (rows 35 322 76 137 176 48 64 128 256), losses := [] }

theorem u1599 : Upper (D 3) (R 3) [34,320,72,129,160,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1599
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 322 76 168 145 33 85 149 277), lower := (rows 35 322 76 168 145 33 64 128 256), losses := [] }

theorem u1600 : Upper (D 3) (R 3) [34,320,72,160,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1600
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 76 168 145 36 81 145 273), lower := (rows 35 322 76 168 145 36 64 128 256), losses := [] }

theorem u1601 : Upper (D 3) (R 3) [34,320,72,160,129,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1601
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 322 76 168 145 48 69 133 261), lower := (rows 35 322 76 168 145 48 64 128 256), losses := [] }

theorem u1602 : Upper (D 3) (R 3) [34,320,72,160,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1602
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 35 322 100 137 148 33 89 153 281), lower := (rows 35 322 100 137 148 33 64 128 256), losses := [] }

theorem u1603 : Upper (D 3) (R 3) [34,320,96,129,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1603
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 322 100 137 148 40 81 145 273), lower := (rows 35 322 100 137 148 40 64 128 256), losses := [] }

theorem u1604 : Upper (D 3) (R 3) [34,320,96,129,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1604
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 322 100 137 148 48 73 137 265), lower := (rows 35 322 100 137 148 48 64 128 256), losses := [] }

theorem u1605 : Upper (D 3) (R 3) [34,320,96,129,132,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1605
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 273 33 224 224 480), lower := (rows 97 7 14 152 273 33 64 128 256), losses := [] }

theorem u1606 : Upper (D 3) (R 3) [96,5,10,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1606
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 152 273 96 225 161 417), lower := (rows 97 7 14 152 273 96 64 128 256), losses := [] }

theorem u1607 : Upper (D 3) (R 3) [96,5,10,144,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1607
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 273 160 97 225 353), lower := (rows 97 7 14 152 273 160 64 128 256), losses := [] }

theorem u1608 : Upper (D 3) (R 3) [96,5,10,144,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1608
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 304 33 193 193 449), lower := (rows 97 7 14 152 304 33 64 128 256), losses := [] }

theorem u1609 : Upper (D 3) (R 3) [96,5,10,144,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1609
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 152 304 96 193 129 385), lower := (rows 97 7 14 152 304 96 64 128 256), losses := [] }

theorem u1610 : Upper (D 3) (R 3) [96,5,10,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1610
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 65, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 152 304 160 65 193 321), lower := (rows 97 7 14 152 304 160 64 128 256), losses := [] }

theorem u1611 : Upper (D 3) (R 3) [96,5,10,144,288,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1611
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 224, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 145 33 224 224 480), lower := (rows 97 7 14 280 145 33 64 128 256), losses := [] }

theorem u1612 : Upper (D 3) (R 3) [96,5,10,272,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1612
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 280 145 96 225 161 417), lower := (rows 97 7 14 280 145 96 64 128 256), losses := [] }

theorem u1613 : Upper (D 3) (R 3) [96,5,10,272,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1613
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 145 160 97 225 353), lower := (rows 97 7 14 280 145 160 64 128 256), losses := [] }

theorem u1614 : Upper (D 3) (R 3) [96,5,10,272,129,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1614
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 193, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 176 33 193 193 449), lower := (rows 97 7 14 280 176 33 64 128 256), losses := [] }

theorem u1615 : Upper (D 3) (R 3) [96,5,10,272,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1615
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 14 280 176 96 193 129 385), lower := (rows 97 7 14 280 176 96 64 128 256), losses := [] }

theorem u1616 : Upper (D 3) (R 3) [96,5,10,272,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1616
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 7 14 280 176 160 65 193 321), lower := (rows 97 7 14 280 176 160 64 128 256), losses := [] }

theorem u1617 : Upper (D 3) (R 3) [96,5,10,272,160,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1617
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 224, camps := [], pairs := [], upper := (rows 97 7 28 137 273 34 224 224 480), lower := (rows 97 7 28 137 273 34 64 128 256), losses := [] }

theorem u1618 : Upper (D 3) (R 3) [96,5,24,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1618
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 162, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 137 273 96 226 162 418), lower := (rows 97 7 28 137 273 96 64 128 256), losses := [] }

theorem u1619 : Upper (D 3) (R 3) [96,5,24,129,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1619
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P03
