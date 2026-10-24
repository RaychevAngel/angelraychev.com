import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 88 274 160 65 160 416), lower := (rows 7 42 69 88 274 160 65 128 256), losses := [] }

theorem u1560 : Upper (D 7) (R 7) [6,40,65,80,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1560 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(2,1),(2,7),(4,5)], upper := (rows 7 42 69 88 274 160 96 129 385), lower := (rows 7 42 69 88 274 160 96 128 256), losses := [] }

theorem u1561 : Upper (D 7) (R 7) [6,40,65,80,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1561 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(1,0),(2,1),(4,6)], upper := (rows 7 42 69 88 274 160 192 161 289), lower := (rows 7 42 69 88 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 6 106 100 122 274 224 224 224 256) },{ target := 5, region := (rows 19 2 14 8 16 0 224 128 256), good := (rows 7 79 69 93 279 192 192 192 256) }] }

theorem u1562 : Upper (D 7) (R 7) [6,40,65,80,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1562 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 434, targets := 65 }], pairs := [(1,0),(1,6),(4,0),(4,6)], upper := (rows 7 42 69 88 304 160 65 130 386), lower := (rows 7 42 69 88 304 160 65 128 256), losses := [] }

theorem u1563 : Upper (D 7) (R 7) [6,40,65,80,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1563 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 88 304 160 66 129 385), lower := (rows 7 42 69 88 304 160 66 128 256), losses := [] }

theorem u1564 : Upper (D 7) (R 7) [6,40,65,80,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1564 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(0,5),(1,0),(2,5),(4,6)], upper := (rows 7 42 69 88 304 160 192 131 259), lower := (rows 7 42 69 88 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 26 4 24 16 224 224 128 256), good := (rows 6 106 100 122 378 224 224 224 256) }] }

theorem u1565 : Upper (D 7) (R 7) [6,40,65,80,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1565 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1566 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 137 112 288 66 144 400), lower := (rows 7 42 69 137 112 288 66 128 256), losses := [] }

theorem u1566 : Upper (D 7) (R 7) [6,40,65,129,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1566 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 69 137 112 288 80 130 386), lower := (rows 7 42 69 137 112 288 80 128 256), losses := [] }

theorem u1567 : Upper (D 7) (R 7) [6,40,65,129,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1567 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 370, targets := 1 },{ cop := 3, region := 68, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 7 42 69 137 112 288 192 146 274), lower := (rows 7 42 69 137 112 288 192 128 256), losses := [] }

theorem u1568 : Upper (D 7) (R 7) [6,40,65,129,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1568 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 137 176 288 66 208 336), lower := (rows 7 42 69 137 176 288 66 128 256), losses := [] }

theorem u1569 : Upper (D 7) (R 7) [6,40,65,129,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1569 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 370, targets := 1 }], pairs := [(1,0),(4,0)], upper := (rows 7 42 69 137 176 288 80 194 322), lower := (rows 7 42 69 137 176 288 80 128 256), losses := [] }

theorem u1570 : Upper (D 7) (R 7) [6,40,65,129,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1570 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 137 208 288 66 176 304), lower := (rows 7 42 69 137 208 288 66 128 256), losses := [] }

theorem u1571 : Upper (D 7) (R 7) [6,40,65,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1571 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 84, targets := 34 }], pairs := [(2,1),(2,5)], upper := (rows 7 42 69 137 208 288 80 162 290), lower := (rows 7 42 69 137 208 288 80 128 256), losses := [] }

theorem u1572 : Upper (D 7) (R 7) [6,40,65,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1572 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 370, targets := 1 }], pairs := [(0,7),(1,0),(2,7)], upper := (rows 7 42 69 137 208 288 96 146 274), lower := (rows 7 42 69 137 208 288 96 128 256), losses := [] }

theorem u1573 : Upper (D 7) (R 7) [6,40,65,129,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1573 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 138 112 288 65 144 400), lower := (rows 7 42 69 138 112 288 65 128 256), losses := [] }

theorem u1574 : Upper (D 7) (R 7) [6,40,65,130,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1574 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 69 138 112 288 80 129 385), lower := (rows 7 42 69 138 112 288 80 128 256), losses := [] }

theorem u1575 : Upper (D 7) (R 7) [6,40,65,130,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1575 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,1),(4,1)], upper := (rows 7 42 69 138 112 288 192 145 273), lower := (rows 7 42 69 138 112 288 192 128 256), losses := [] }

theorem u1576 : Upper (D 7) (R 7) [6,40,65,130,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1576 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 138 208 288 65 176 304), lower := (rows 7 42 69 138 208 288 65 128 256), losses := [] }

theorem u1577 : Upper (D 7) (R 7) [6,40,65,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1577 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 69 138 208 288 80 161 289), lower := (rows 7 42 69 138 208 288 80 128 256), losses := [] }

theorem u1578 : Upper (D 7) (R 7) [6,40,65,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1578 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(4,1)], upper := (rows 7 42 69 138 208 288 96 145 273), lower := (rows 7 42 69 138 208 288 96 128 256), losses := [] }

theorem u1579 : Upper (D 7) (R 7) [6,40,65,130,192,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1579 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 304 96 65 144 400), lower := (rows 7 42 69 138 304 96 65 128 256), losses := [] }

theorem u1580 : Upper (D 7) (R 7) [6,40,65,130,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1580 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 42 69 138 304 96 80 129 385), lower := (rows 7 42 69 138 304 96 80 128 256), losses := [] }

theorem u1581 : Upper (D 7) (R 7) [6,40,65,130,288,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1581 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,1),(2,5),(4,1)], upper := (rows 7 42 69 138 304 96 192 145 273), lower := (rows 7 42 69 138 304 96 192 128 256), losses := [] }

theorem u1582 : Upper (D 7) (R 7) [6,40,65,130,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1582 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 138 336 48 65 160 416), lower := (rows 7 42 69 138 336 48 65 128 256), losses := [] }

theorem u1583 : Upper (D 7) (R 7) [6,40,65,130,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1583 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 129, camps := [{ cop := 8, region := 112, targets := 131 }], pairs := [(4,0),(4,1),(4,7)], upper := (rows 7 42 69 138 336 48 96 129 385), lower := (rows 7 42 69 138 336 48 96 128 256), losses := [] }

theorem u1584 : Upper (D 7) (R 7) [6,40,65,130,320,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1584 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 3, region := 69, targets := 32 }], pairs := [(0,5),(2,1),(4,1)], upper := (rows 7 42 69 138 336 48 192 161 289), lower := (rows 7 42 69 138 336 48 192 128 256), losses := [] }

theorem u1585 : Upper (D 7) (R 7) [6,40,65,130,320,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1585 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 138 400 96 65 176 304), lower := (rows 7 42 69 138 400 96 65 128 256), losses := [] }

theorem u1586 : Upper (D 7) (R 7) [6,40,65,130,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1586 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,1),(4,1)], upper := (rows 7 42 69 138 400 96 80 161 289), lower := (rows 7 42 69 138 400 96 80 128 256), losses := [] }

theorem u1587 : Upper (D 7) (R 7) [6,40,65,130,384,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1587 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 138 400 96 96 145 273), lower := (rows 7 42 69 138 400 96 96 128 256), losses := [] }

theorem u1588 : Upper (D 7) (R 7) [6,40,65,130,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1588 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 69 152 112 288 65 130 386), lower := (rows 7 42 69 152 112 288 65 128 256), losses := [] }

theorem u1589 : Upper (D 7) (R 7) [6,40,65,144,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1589 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 69 152 112 288 66 129 385), lower := (rows 7 42 69 152 112 288 66 128 256), losses := [] }

theorem u1590 : Upper (D 7) (R 7) [6,40,65,144,96,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1590 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0)], upper := (rows 7 42 69 152 112 288 192 131 259), lower := (rows 7 42 69 152 112 288 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 288 200 128 256), good := (rows 22 122 68 216 112 288 192 192 288) }] }

theorem u1591 : Upper (D 7) (R 7) [6,40,65,144,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1591 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 152 274 96 65 160 416), lower := (rows 7 42 69 152 274 96 65 128 256), losses := [] }

theorem u1592 : Upper (D 7) (R 7) [6,40,65,144,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1592 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 152 274 96 96 129 385), lower := (rows 7 42 69 152 274 96 96 128 256), losses := [] }

theorem u1593 : Upper (D 7) (R 7) [6,40,65,144,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1593 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1594 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 228, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,1),(2,5)], upper := (rows 7 42 69 152 274 96 192 161 289), lower := (rows 7 42 69 152 274 96 192 128 256), losses := [{ target := 5, region := (rows 19 2 14 8 16 0 200 128 256), good := (rows 7 79 69 221 279 64 192 192 256) }] }

theorem u1594 : Upper (D 7) (R 7) [6,40,65,144,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1594 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 152 304 96 65 130 386), lower := (rows 7 42 69 152 304 96 65 128 256), losses := [] }

theorem u1595 : Upper (D 7) (R 7) [6,40,65,144,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1595 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 42 69 152 304 96 66 129 385), lower := (rows 7 42 69 152 304 96 66 128 256), losses := [] }

theorem u1596 : Upper (D 7) (R 7) [6,40,65,144,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1596 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 98, targets := 1 }], pairs := [(0,5),(1,0),(2,5),(4,7)], upper := (rows 7 42 69 152 304 96 192 131 259), lower := (rows 7 42 69 152 304 96 192 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 21 100 64 0 257), good := (rows 311 42 373 24 304 96 96 0 256) }] }

theorem u1597 : Upper (D 7) (R 7) [6,40,65,144,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1597 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 152 336 33 66 160 416), lower := (rows 7 42 69 152 336 33 66 128 256), losses := [] }

theorem u1598 : Upper (D 7) (R 7) [6,40,65,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1598 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 152 336 33 96 130 386), lower := (rows 7 42 69 152 336 33 96 128 256), losses := [] }

theorem u1599 : Upper (D 7) (R 7) [6,40,65,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1599 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(0,5),(1,0),(3,0),(4,0)], upper := (rows 7 42 69 152 336 33 192 162 290), lower := (rows 7 42 69 152 336 33 192 128 256), losses := [{ target := 5, region := (rows 3 2 6 8 16 0 200 128 256), good := (rows 7 79 69 216 336 1 192 192 256) }] }

theorem u1600 : Upper (D 7) (R 7) [6,40,65,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1600 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 170, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 152 336 34 65 160 416), lower := (rows 7 42 69 152 336 34 65 128 256), losses := [] }

theorem u1601 : Upper (D 7) (R 7) [6,40,65,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1601 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 69 152 336 34 96 129 385), lower := (rows 7 42 69 152 336 34 96 128 256), losses := [] }

theorem u1602 : Upper (D 7) (R 7) [6,40,65,144,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1602 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 34, targets := 192 },{ cop := 3, region := 34, targets := 1 }], pairs := [(0,5),(1,0),(1,6),(1,7)], upper := (rows 7 42 69 152 336 34 192 161 289), lower := (rows 7 42 69 152 336 34 192 128 256), losses := [{ target := 5, region := (rows 35 2 6 8 16 0 200 128 256), good := (rows 7 79 69 216 336 7 192 192 256) }] }

theorem u1603 : Upper (D 7) (R 7) [6,40,65,144,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1603 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 200 176 288 65 146 274), lower := (rows 7 42 69 200 176 288 65 128 256), losses := [] }

theorem u1604 : Upper (D 7) (R 7) [6,40,65,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1604 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 200 176 288 66 145 273), lower := (rows 7 42 69 200 176 288 66 128 256), losses := [] }

theorem u1605 : Upper (D 7) (R 7) [6,40,65,192,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1605 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 69 200 176 288 80 131 259), lower := (rows 7 42 69 200 176 288 80 128 256), losses := [] }

theorem u1606 : Upper (D 7) (R 7) [6,40,65,192,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1606 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 200 274 48 65 160 416), lower := (rows 7 42 69 200 274 48 65 128 256), losses := [] }

theorem u1607 : Upper (D 7) (R 7) [6,40,65,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1607 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 136, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 7 42 69 200 274 48 96 129 385), lower := (rows 7 42 69 200 274 48 96 128 256), losses := [] }

theorem u1608 : Upper (D 7) (R 7) [6,40,65,192,258,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1608 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 200 274 48 192 161 289), lower := (rows 7 42 69 200 274 48 192 128 256), losses := [] }

theorem u1609 : Upper (D 7) (R 7) [6,40,65,192,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1609 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 265 112 160 66 144 400), lower := (rows 7 42 69 265 112 160 66 128 256), losses := [] }

theorem u1610 : Upper (D 7) (R 7) [6,40,65,257,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1610 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 69 265 112 160 80 130 386), lower := (rows 7 42 69 265 112 160 80 128 256), losses := [] }

theorem u1611 : Upper (D 7) (R 7) [6,40,65,257,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1611 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 265 112 160 192 146 274), lower := (rows 7 42 69 265 112 160 192 128 256), losses := [] }

theorem u1612 : Upper (D 7) (R 7) [6,40,65,257,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1612 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 265 146 160 80 224 352), lower := (rows 7 42 69 265 146 160 80 128 256), losses := [] }

theorem u1613 : Upper (D 7) (R 7) [6,40,65,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1613 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 265 146 160 96 208 336), lower := (rows 7 42 69 265 146 160 96 128 256), losses := [] }

theorem u1614 : Upper (D 7) (R 7) [6,40,65,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1614 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 265 208 160 66 176 304), lower := (rows 7 42 69 265 208 160 66 128 256), losses := [] }

theorem u1615 : Upper (D 7) (R 7) [6,40,65,257,192,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1615 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 69 265 208 160 80 162 290), lower := (rows 7 42 69 265 208 160 80 128 256), losses := [] }

theorem u1616 : Upper (D 7) (R 7) [6,40,65,257,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1616 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 3, region := 242, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,0)], upper := (rows 7 42 69 265 208 160 96 146 274), lower := (rows 7 42 69 265 208 160 96 128 256), losses := [] }

theorem u1617 : Upper (D 7) (R 7) [6,40,65,257,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1617 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 266 112 160 65 144 400), lower := (rows 7 42 69 266 112 160 65 128 256), losses := [] }

theorem u1618 : Upper (D 7) (R 7) [6,40,65,258,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1618 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 69 266 112 160 80 129 385), lower := (rows 7 42 69 266 112 160 80 128 256), losses := [] }

theorem u1619 : Upper (D 7) (R 7) [6,40,65,258,96,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1619 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P07
