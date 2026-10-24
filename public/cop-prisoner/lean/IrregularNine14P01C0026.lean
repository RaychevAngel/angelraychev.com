import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P01C0003

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 469, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 69 138 144 34 112 240 368), lower := (rows 277 42 69 138 144 34 64 128 256), losses := [] }

theorem u1560 : Upper (D 1) (R 1) [276,40,65,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1560
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 138 144 48 98 226 354), lower := (rows 277 42 69 138 144 48 64 128 256), losses := [] }

theorem u1561 : Upper (D 1) (R 1) [276,40,65,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1561
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 50, camps := [{ cop := 5, region := 154, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 69 138 144 96 114 178 306), lower := (rows 277 42 69 138 144 96 64 128 256), losses := [] }

theorem u1562 : Upper (D 1) (R 1) [276,40,65,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1562
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 70 137 48 34 208 208 464), lower := (rows 277 42 70 137 48 34 64 128 256), losses := [] }

theorem u1563 : Upper (D 1) (R 1) [276,40,66,129,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1563
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 194, camps := [{ cop := 1, region := 196, targets := 16 }], pairs := [(2,4)], upper := (rows 277 42 70 137 48 48 194 194 450), lower := (rows 277 42 70 137 48 48 64 128 256), losses := [] }

theorem u1564 : Upper (D 1) (R 1) [276,40,66,129,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1564
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 146, camps := [], pairs := [(0,6)], upper := (rows 277 42 70 137 48 96 210 146 402), lower := (rows 277 42 70 137 48 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 50 32 0 134 262), good := (rows 413 442 415 137 48 48 0 128 256) }] }

theorem u1565 : Upper (D 1) (R 1) [276,40,66,129,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1565
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 70 137 48 160 82 210 338), lower := (rows 277 42 70 137 48 160 64 128 256), losses := [] }

theorem u1566 : Upper (D 1) (R 1) [276,40,66,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1566
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 70 137 144 34 112 240 368), lower := (rows 277 42 70 137 144 34 64 128 256), losses := [] }

theorem u1567 : Upper (D 1) (R 1) [276,40,66,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1567
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 68, targets := 16 }], pairs := [(2,4)], upper := (rows 277 42 70 137 144 48 98 226 354), lower := (rows 277 42 70 137 144 48 64 128 256), losses := [] }

theorem u1568 : Upper (D 1) (R 1) [276,40,66,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1568
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 50, camps := [], pairs := [(0,6)], upper := (rows 277 42 70 137 144 96 114 178 306), lower := (rows 277 42 70 137 144 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 12 158 32 0 130 258), good := (rows 285 442 415 153 144 32 0 144 256) }] }

theorem u1569 : Upper (D 1) (R 1) [276,40,66,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1569
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 42 70 152 48 33 194 194 450), lower := (rows 277 42 70 152 48 33 64 128 256), losses := [] }

theorem u1570 : Upper (D 1) (R 1) [276,40,66,144,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1570
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 70 152 48 34 193 193 449), lower := (rows 277 42 70 152 48 34 64 128 256), losses := [] }

theorem u1571 : Upper (D 1) (R 1) [276,40,66,144,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1571
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 131, camps := [], pairs := [(0,6)], upper := (rows 277 42 70 152 48 96 195 131 387), lower := (rows 277 42 70 152 48 96 64 128 256), losses := [{ target := 6, region := (rows 5 2 4 13 50 32 0 132 260), good := (rows 413 58 415 152 48 48 0 128 256) }] }

theorem u1572 : Upper (D 1) (R 1) [276,40,66,144,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1572
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 70 152 48 160 67 195 323), lower := (rows 277 42 70 152 48 160 64 128 256), losses := [] }

theorem u1573 : Upper (D 1) (R 1) [276,40,66,144,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1573
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 42, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 100 11 144 34 208 208 464), lower := (rows 277 42 100 11 144 34 64 128 256), losses := [] }

theorem u1574 : Upper (D 1) (R 1) [276,40,96,3,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1574
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 11 144 48 194 194 450), lower := (rows 277 42 100 11 144 48 64 128 256), losses := [] }

theorem u1575 : Upper (D 1) (R 1) [276,40,96,3,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1575
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 146, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 100 11 144 96 210 146 402), lower := (rows 277 42 100 11 144 96 64 128 256), losses := [] }

theorem u1576 : Upper (D 1) (R 1) [276,40,96,3,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1576
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 82, camps := [], pairs := [(1,4)], upper := (rows 277 42 100 11 144 160 82 210 338), lower := (rows 277 42 100 11 144 160 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 9 0 176 64 128 256), good := (rows 303 42 100 11 160 160 64 160 256) }] }

theorem u1577 : Upper (D 1) (R 1) [276,40,96,3,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1577
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 42 100 26 144 33 194 194 450), lower := (rows 277 42 100 26 144 33 64 128 256), losses := [] }

theorem u1578 : Upper (D 1) (R 1) [276,40,96,18,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1578
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 26 144 34 193 193 449), lower := (rows 277 42 100 26 144 34 64 128 256), losses := [] }

theorem u1579 : Upper (D 1) (R 1) [276,40,96,18,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1579
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 100 26 144 96 195 131 387), lower := (rows 277 42 100 26 144 96 64 128 256), losses := [] }

theorem u1580 : Upper (D 1) (R 1) [276,40,96,18,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1580
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 26 144 160 67 195 323), lower := (rows 277 42 100 26 144 160 64 128 256), losses := [] }

theorem u1581 : Upper (D 1) (R 1) [276,40,96,18,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1581
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 277 42 100 88 144 33 194 130 386), lower := (rows 277 42 100 88 144 33 64 128 256), losses := [] }

theorem u1582 : Upper (D 1) (R 1) [276,40,96,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1582
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 100 88 144 34 195 131 387), lower := (rows 277 42 100 88 144 34 64 128 256), losses := [] }

theorem u1583 : Upper (D 1) (R 1) [276,40,96,80,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1583
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 3, camps := [], pairs := [(2,1)], upper := (rows 277 42 100 88 144 160 67 131 259), lower := (rows 277 42 100 88 144 160 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 12 176 176 64 128 256), good := (rows 317 60 124 124 176 176 64 176 256) }] }

theorem u1584 : Upper (D 1) (R 1) [276,40,96,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1584
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 82, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 100 137 144 34 82 210 338), lower := (rows 277 42 100 137 144 34 64 128 256), losses := [] }

theorem u1585 : Upper (D 1) (R 1) [276,40,96,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1585
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 68, targets := 16 }], pairs := [(2,4)], upper := (rows 277 42 100 137 144 48 66 194 322), lower := (rows 277 42 100 137 144 48 64 128 256), losses := [] }

theorem u1586 : Upper (D 1) (R 1) [276,40,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1586
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 100 137 144 96 82 146 274), lower := (rows 277 42 100 137 144 96 64 128 256), losses := [] }

theorem u1587 : Upper (D 1) (R 1) [276,40,96,129,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1587
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 82, camps := [], pairs := [], upper := (rows 277 42 100 138 144 33 82 210 338), lower := (rows 277 42 100 138 144 33 64 128 256), losses := [] }

theorem u1588 : Upper (D 1) (R 1) [276,40,96,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1588
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 469, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 100 138 144 34 81 209 337), lower := (rows 277 42 100 138 144 34 64 128 256), losses := [] }

theorem u1589 : Upper (D 1) (R 1) [276,40,96,130,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1589
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 67, camps := [{ cop := 4, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 100 138 144 48 67 195 323), lower := (rows 277 42 100 138 144 48 64 128 256), losses := [] }

theorem u1590 : Upper (D 1) (R 1) [276,40,96,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1590
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 100 138 144 96 83 147 275), lower := (rows 277 42 100 138 144 96 64 128 256), losses := [] }

theorem u1591 : Upper (D 1) (R 1) [276,40,96,130,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1591
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 42 100 152 18 33 194 194 450), lower := (rows 277 42 100 152 18 33 64 128 256), losses := [] }

theorem u1592 : Upper (D 1) (R 1) [276,40,96,144,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1592
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 193, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 100 152 18 34 193 193 449), lower := (rows 277 42 100 152 18 34 64 128 256), losses := [] }

theorem u1593 : Upper (D 1) (R 1) [276,40,96,144,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1593
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 277 42 100 152 18 96 195 131 387), lower := (rows 277 42 100 152 18 96 64 128 256), losses := [] }

theorem u1594 : Upper (D 1) (R 1) [276,40,96,144,2,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1594
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 67, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 100 152 18 160 67 195 323), lower := (rows 277 42 100 152 18 160 64 128 256), losses := [] }

theorem u1595 : Upper (D 1) (R 1) [276,40,96,144,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1595
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 42 100 200 18 33 210 146 402), lower := (rows 277 42 100 200 18 33 64 128 256), losses := [] }

theorem u1596 : Upper (D 1) (R 1) [276,40,96,192,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1596
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 200, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 100 200 18 34 209 145 401), lower := (rows 277 42 100 200 18 34 64 128 256), losses := [] }

theorem u1597 : Upper (D 1) (R 1) [276,40,96,192,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1597
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 50, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 100 200 18 48 195 131 387), lower := (rows 277 42 100 200 18 48 64 128 256), losses := [] }

theorem u1598 : Upper (D 1) (R 1) [276,40,96,192,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1598
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 19, camps := [{ cop := 1, region := 341, targets := 128 }], pairs := [(0,7)], upper := (rows 277 42 100 200 18 160 83 147 275), lower := (rows 277 42 100 200 18 160 64 128 256), losses := [] }

theorem u1599 : Upper (D 1) (R 1) [276,40,96,192,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1599
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 277 42 100 200 144 33 82 146 274), lower := (rows 277 42 100 200 144 33 64 128 256), losses := [] }

theorem u1600 : Upper (D 1) (R 1) [276,40,96,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1600
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 34, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 100 200 144 34 83 147 275), lower := (rows 277 42 100 200 144 34 64 128 256), losses := [] }

theorem u1601 : Upper (D 1) (R 1) [276,40,96,192,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1601
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 52, targets := 2 }], pairs := [(2,1)], upper := (rows 277 42 100 200 144 48 67 131 259), lower := (rows 277 42 100 200 144 48 64 128 256), losses := [] }

theorem u1602 : Upper (D 1) (R 1) [276,40,96,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1602
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 11 48 34 208 208 464), lower := (rows 277 42 196 11 48 34 64 128 256), losses := [] }

theorem u1603 : Upper (D 1) (R 1) [276,40,192,3,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1603
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 42, targets := 64 }], pairs := [(1,6)], upper := (rows 277 42 196 11 48 48 194 194 450), lower := (rows 277 42 196 11 48 48 64 128 256), losses := [] }

theorem u1604 : Upper (D 1) (R 1) [276,40,192,3,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1604
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 146, camps := [], pairs := [(1,4)], upper := (rows 277 42 196 11 48 96 210 146 402), lower := (rows 277 42 196 11 48 96 64 128 256), losses := [{ target := 4, region := (rows 1 3 4 9 0 100 64 128 256), good := (rows 303 42 228 11 32 96 96 128 256) }] }

theorem u1605 : Upper (D 1) (R 1) [276,40,192,3,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1605
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 146, camps := [], pairs := [], upper := (rows 277 42 196 74 48 33 210 146 402), lower := (rows 277 42 196 74 48 33 64 128 256), losses := [] }

theorem u1606 : Upper (D 1) (R 1) [276,40,192,66,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1606
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 145, camps := [{ cop := 4, region := 453, targets := 2 }], pairs := [(0,1)], upper := (rows 277 42 196 74 48 34 209 145 401), lower := (rows 277 42 196 74 48 34 64 128 256), losses := [] }

theorem u1607 : Upper (D 1) (R 1) [276,40,192,66,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1607
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 58, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 196 74 48 48 195 131 387), lower := (rows 277 42 196 74 48 48 64 128 256), losses := [] }

theorem u1608 : Upper (D 1) (R 1) [276,40,192,66,32,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1608
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 42, targets := 16 }], pairs := [(1,4)], upper := (rows 277 42 196 74 48 160 83 147 275), lower := (rows 277 42 196 74 48 160 64 128 256), losses := [] }

theorem u1609 : Upper (D 1) (R 1) [276,40,192,66,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1609
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 162, camps := [], pairs := [], upper := (rows 277 42 196 88 18 33 226 162 418), lower := (rows 277 42 196 88 18 33 64 128 256), losses := [] }

theorem u1610 : Upper (D 1) (R 1) [276,40,192,80,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1610
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 58, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 196 88 18 34 225 161 417), lower := (rows 277 42 196 88 18 34 64 128 256), losses := [] }

theorem u1611 : Upper (D 1) (R 1) [276,40,192,80,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1611
    (constants 1).1 (constants 1).2 (by decide +kernel)

def r1612 : Route 9 := (fun mask => (mask,id))

def c1612 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1612 : Upper (D 1) (R 1) [276,40,192,80,2,128] 13 := by
  apply FastRouting.sound _ _ [276,40,192,80,2,128] 13 (by decide) (choices 1) [1,2,32] r1612 c1612
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u193
  · exact u194
  · exact u195

def b1613 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 277 42 196 88 48 33 194 130 386), lower := (rows 277 42 196 88 48 33 64 128 256), losses := [] }

theorem u1613 : Upper (D 1) (R 1) [276,40,192,80,32,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1613
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 131, camps := [{ cop := 2, region := 58, targets := 128 }], pairs := [(1,7)], upper := (rows 277 42 196 88 48 34 195 131 387), lower := (rows 277 42 196 88 48 34 64 128 256), losses := [] }

theorem u1614 : Upper (D 1) (R 1) [276,40,192,80,32,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1614
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 56, targets := 2 }], pairs := [(3,1)], upper := (rows 277 42 196 88 48 160 67 131 259), lower := (rows 277 42 196 88 48 160 64 128 256), losses := [] }

theorem u1615 : Upper (D 1) (R 1) [276,40,192,80,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1615
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 194, camps := [{ cop := 0, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 277 50 44 73 144 34 194 194 450), lower := (rows 277 50 44 73 144 34 64 128 256), losses := [] }

theorem u1616 : Upper (D 1) (R 1) [276,48,40,65,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1616
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 36, targets := 2 }], pairs := [(2,1)], upper := (rows 277 50 44 73 144 96 194 130 386), lower := (rows 277 50 44 73 144 96 64 128 256), losses := [] }

theorem u1617 : Upper (D 1) (R 1) [276,48,40,65,128,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1617
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 66, camps := [{ cop := 1, region := 333, targets := 128 }], pairs := [(0,7)], upper := (rows 277 50 44 73 144 160 66 194 322), lower := (rows 277 50 44 73 144 160 64 128 256), losses := [] }

theorem u1618 : Upper (D 1) (R 1) [276,48,40,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1618
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 194, camps := [], pairs := [], upper := (rows 277 50 44 74 144 33 194 194 450), lower := (rows 277 50 44 74 144 33 64 128 256), losses := [] }

theorem u1619 : Upper (D 1) (R 1) [276,48,40,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b1619
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P01
