import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0003

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 292 56 208 40 193 129 385), lower := (rows 7 98 292 56 208 40 64 128 256), losses := [] }

theorem u1560 : Upper (D 8) (R 8) [6,96,288,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1560 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 9, camps := [{ cop := 3, region := 327, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 56 208 160 73 137 265), lower := (rows 7 98 292 56 208 160 64 128 256), losses := [] }

theorem u1561 : Upper (D 8) (R 8) [6,96,288,48,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1561 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 168, camps := [], pairs := [(2,6)], upper := (rows 7 98 292 88 145 33 232 168 424), lower := (rows 7 98 292 88 145 33 64 128 256), losses := [{ target := 6, region := (rows 1 2 12 8 16 49 0 136 264), good := (rows 39 34 292 444 177 33 0 128 256) }] }

theorem u1562 : Upper (D 8) (R 8) [6,96,288,80,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1562 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 292 88 145 40 225 161 417), lower := (rows 7 98 292 88 145 40 64 128 256), losses := [] }

theorem u1563 : Upper (D 8) (R 8) [6,96,288,80,129,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1563 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 41, camps := [], pairs := [(1,0)], upper := (rows 7 98 292 88 145 160 105 169 297), lower := (rows 7 98 292 88 145 160 64 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 176 64 128 256), good := (rows 6 98 292 122 176 160 64 160 256) }] }

theorem u1564 : Upper (D 8) (R 8) [6,96,288,80,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1564 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1565 : Route 9 := (fun mask => (mask,id))

def c1565 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1565 : Upper (D 8) (R 8) [6,96,288,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,80,160,1] 13 (by decide) (choices 1) [1,8,128] r1565 c1565
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u213
  · exact u214
  · exact u215

def b1566 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 7 98 292 88 176 40 193 129 385), lower := (rows 7 98 292 88 176 40 64 128 256), losses := [] }

theorem u1566 : Upper (D 8) (R 8) [6,96,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1566 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1567 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 7 98 292 88 176 160 73 137 265), lower := (rows 7 98 292 88 176 160 64 128 256), losses := [] }

theorem u1567 : Upper (D 8) (R 8) [6,96,288,80,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1567 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 48, targets := 64 }], pairs := [(4,6)], upper := (rows 7 98 292 137 176 33 88 216 344), lower := (rows 7 98 292 137 176 33 64 128 256), losses := [] }

theorem u1568 : Upper (D 8) (R 8) [6,96,288,129,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1568 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 98 292 137 176 40 81 209 337), lower := (rows 7 98 292 137 176 40 64 128 256), losses := [] }

theorem u1569 : Upper (D 8) (R 8) [6,96,288,129,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1569 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 7 98 292 137 176 48 73 201 329), lower := (rows 7 98 292 137 176 48 64 128 256), losses := [] }

theorem u1570 : Upper (D 8) (R 8) [6,96,288,129,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1570 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 292 137 176 96 89 153 281), lower := (rows 7 98 292 137 176 96 64 128 256), losses := [] }

theorem u1571 : Upper (D 8) (R 8) [6,96,288,129,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1571 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1572 : Route 9 := (fun mask => (mask,id))

def c1572 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1572 : Upper (D 8) (R 8) [6,96,288,129,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,129,192,1] 13 (by decide) (choices 1) [8,16,32] r1572 c1572
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u216
  · exact u217
  · exact u218

def b1573 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 98 292 137 208 40 113 177 305), lower := (rows 7 98 292 137 208 40 64 128 256), losses := [] }

theorem u1573 : Upper (D 8) (R 8) [6,96,288,129,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1573 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 98 292 137 208 48 105 169 297), lower := (rows 7 98 292 137 208 48 64 128 256), losses := [] }

theorem u1574 : Upper (D 8) (R 8) [6,96,288,129,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1574 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1575 : Route 9 := (fun mask => (mask,id))

def c1575 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1575 : Upper (D 8) (R 8) [6,96,288,160,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,288,160,192,1] 13 (by decide) (choices 1) [1,8,16] r1575 c1575
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u219
  · exact u220
  · exact u221

def b1576 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 98 292 168 208 40 81 145 273), lower := (rows 7 98 292 168 208 40 64 128 256), losses := [] }

theorem u1576 : Upper (D 8) (R 8) [6,96,288,160,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1576 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1577 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 7 98 292 168 208 48 73 137 265), lower := (rows 7 98 292 168 208 48 64 128 256), losses := [] }

theorem u1577 : Upper (D 8) (R 8) [6,96,288,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1577 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1578 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 98 388 25 56 33 224 224 480), lower := (rows 7 98 388 25 56 33 64 128 256), losses := [] }

theorem u1578 : Upper (D 8) (R 8) [6,96,384,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1578 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 161, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 25 56 96 225 161 417), lower := (rows 7 98 388 25 56 96 64 128 256), losses := [] }

theorem u1579 : Upper (D 8) (R 8) [6,96,384,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1579 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 97, camps := [], pairs := [(3,6)], upper := (rows 7 98 388 25 56 160 97 225 353), lower := (rows 7 98 388 25 56 160 64 128 256), losses := [{ target := 6, region := (rows 1 2 4 9 17 164 0 128 256), good := (rows 63 34 420 25 56 160 0 160 256) }] }

theorem u1580 : Upper (D 8) (R 8) [6,96,384,17,40,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1580 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 41 88 33 240 176 432), lower := (rows 7 98 388 41 88 33 64 128 256), losses := [] }

theorem u1581 : Upper (D 8) (R 8) [6,96,384,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1581 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 98 388 41 88 48 225 161 417), lower := (rows 7 98 388 41 88 48 64 128 256), losses := [] }

theorem u1582 : Upper (D 8) (R 8) [6,96,384,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1582 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 82, targets := 128 }], pairs := [(1,7)], upper := (rows 7 98 388 41 88 160 113 177 305), lower := (rows 7 98 388 41 88 160 64 128 256), losses := [] }

theorem u1583 : Upper (D 8) (R 8) [6,96,384,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1583 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 41 152 33 112 240 368), lower := (rows 7 98 388 41 152 33 64 128 256), losses := [] }

theorem u1584 : Upper (D 8) (R 8) [6,96,384,33,136,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1584 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1585 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 7 98 388 41 152 48 97 225 353), lower := (rows 7 98 388 41 152 48 64 128 256), losses := [] }

theorem u1585 : Upper (D 8) (R 8) [6,96,384,33,136,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1585 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1586 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 41 152 96 113 177 305), lower := (rows 7 98 388 41 152 96 64 128 256), losses := [] }

theorem u1586 : Upper (D 8) (R 8) [6,96,384,33,136,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1586 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 88, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 41 176 33 88 216 344), lower := (rows 7 98 388 41 176 33 64 128 256), losses := [] }

theorem u1587 : Upper (D 8) (R 8) [6,96,384,33,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1587 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1588 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 7 98 388 41 176 40 81 209 337), lower := (rows 7 98 388 41 176 40 64 128 256), losses := [] }

theorem u1588 : Upper (D 8) (R 8) [6,96,384,33,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1588 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1589 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 7 98 388 41 176 48 73 201 329), lower := (rows 7 98 388 41 176 48 64 128 256), losses := [] }

theorem u1589 : Upper (D 8) (R 8) [6,96,384,33,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1589 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1590 : PairBound 9 := { available := 25, camps := [{ cop := 1, region := 413, targets := 64 }], pairs := [(0,6)], upper := (rows 7 98 388 41 176 96 89 153 281), lower := (rows 7 98 388 41 176 96 64 128 256), losses := [] }

theorem u1590 : Upper (D 8) (R 8) [6,96,384,33,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1590 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1591 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 98 388 41 208 33 120 184 312), lower := (rows 7 98 388 41 208 33 64 128 256), losses := [] }

theorem u1591 : Upper (D 8) (R 8) [6,96,384,33,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1591 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1592 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 98 388 41 208 40 113 177 305), lower := (rows 7 98 388 41 208 40 64 128 256), losses := [] }

theorem u1592 : Upper (D 8) (R 8) [6,96,384,33,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1592 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1593 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 7 98 388 41 208 48 105 169 297), lower := (rows 7 98 388 41 208 48 64 128 256), losses := [] }

theorem u1593 : Upper (D 8) (R 8) [6,96,384,33,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1593 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1594 : Route 9 := (fun mask => (mask,id))

def c1594 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1594 : Upper (D 8) (R 8) [6,96,384,48,192,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192,1] 13 (by decide) (choices 1) [1,8,32] r1594 c1594
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u222
  · exact u223
  · exact u224

def b1595 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 388 56 208 40 97 161 289), lower := (rows 7 98 388 56 208 40 64 128 256), losses := [] }

theorem u1595 : Upper (D 8) (R 8) [6,96,384,48,192,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1595 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1596 : Route 9 := (fun mask => (mask,id))

def c1596 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1596 : Upper (D 8) (R 8) [6,96,384,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80,160,1] 13 (by decide) (choices 1) [1,8,32] r1596 c1596
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u225
  · exact u226
  · exact u227

def b1597 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 98 388 88 176 40 97 161 289), lower := (rows 7 98 388 88 176 40 64 128 256), losses := [] }

theorem u1597 : Upper (D 8) (R 8) [6,96,384,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1597 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 88 176 33 104 168 296), lower := (rows 7 194 261 88 176 33 64 128 256), losses := [] }

theorem u1598 : Upper (D 8) (R 8) [6,192,257,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1598 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 194 261 88 176 40 97 161 289), lower := (rows 7 194 261 88 176 40 64 128 256), losses := [] }

theorem u1599 : Upper (D 8) (R 8) [6,192,257,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1599 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1600 : PairBound 9 := { available := 56, camps := [{ cop := 5, region := 218, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 261 104 176 33 120 184 312), lower := (rows 7 194 261 104 176 33 64 128 256), losses := [] }

theorem u1600 : Upper (D 8) (R 8) [6,192,257,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1600 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1601 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 7 194 261 104 176 40 113 177 305), lower := (rows 7 194 261 104 176 40 64 128 256), losses := [] }

theorem u1601 : Upper (D 8) (R 8) [6,192,257,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1601 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 268 41 112 33 240 176 432), lower := (rows 7 194 268 41 112 33 64 128 256), losses := [] }

theorem u1602 : Upper (D 8) (R 8) [6,192,264,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1602 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1603 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 194 268 41 112 48 225 161 417), lower := (rows 7 194 268 41 112 48 64 128 256), losses := [] }

theorem u1603 : Upper (D 8) (R 8) [6,192,264,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1603 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1604 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 7 194 268 41 112 160 113 177 305), lower := (rows 7 194 268 41 112 160 64 128 256), losses := [] }

theorem u1604 : Upper (D 8) (R 8) [6,192,264,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1604 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 56, targets := 64 }], pairs := [(3,6)], upper := (rows 7 194 292 25 56 33 224 224 480), lower := (rows 7 194 292 25 56 33 64 128 256), losses := [] }

theorem u1605 : Upper (D 8) (R 8) [6,192,288,17,40,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1605 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 161, camps := [], pairs := [(3,7)], upper := (rows 7 194 292 25 56 96 225 161 417), lower := (rows 7 194 292 25 56 96 64 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 17 98 64 0 256), good := (rows 63 98 292 25 56 96 96 0 256) }] }

theorem u1606 : Upper (D 8) (R 8) [6,192,288,17,40,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1606 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 176, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 292 41 88 33 240 176 432), lower := (rows 7 194 292 41 88 33 64 128 256), losses := [] }

theorem u1607 : Upper (D 8) (R 8) [6,192,288,33,72,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1607 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 7 194 292 41 88 48 225 161 417), lower := (rows 7 194 292 41 88 48 64 128 256), losses := [] }

theorem u1608 : Upper (D 8) (R 8) [6,192,288,33,72,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1608 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 7 194 292 41 88 160 113 177 305), lower := (rows 7 194 292 41 88 160 64 128 256), losses := [] }

theorem u1609 : Upper (D 8) (R 8) [6,192,288,33,72,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1609 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 152, camps := [{ cop := 3, region := 210, targets := 1 }], pairs := [(1,0)], upper := (rows 7 194 292 41 112 33 216 152 408), lower := (rows 7 194 292 41 112 33 64 128 256), losses := [] }

theorem u1610 : Upper (D 8) (R 8) [6,192,288,33,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1610 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 7 194 292 41 112 40 209 145 401), lower := (rows 7 194 292 41 112 40 64 128 256), losses := [] }

theorem u1611 : Upper (D 8) (R 8) [6,192,288,33,96,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1611 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 137, camps := [], pairs := [], upper := (rows 7 194 292 41 112 48 201 137 393), lower := (rows 7 194 292 41 112 48 64 128 256), losses := [] }

theorem u1612 : Upper (D 8) (R 8) [6,192,288,33,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1612 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 25, camps := [{ cop := 3, region := 340, targets := 128 }], pairs := [(2,7)], upper := (rows 7 194 292 41 112 160 89 153 281), lower := (rows 7 194 292 41 112 160 64 128 256), losses := [] }

theorem u1613 : Upper (D 8) (R 8) [6,192,288,33,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1613 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1614 : Route 9 := (fun mask => (mask,id))

def c1614 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1614 : Upper (D 8) (R 8) [6,192,288,80,160,1] 13 := by
  apply FastRouting.sound _ _ [6,192,288,80,160,1] 13 (by decide) (choices 1) [1,8,32] r1614 c1614
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u228
  · exact u229
  · exact u230

def b1615 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 7 194 292 88 176 40 97 161 289), lower := (rows 7 194 292 88 176 40 64 128 256), losses := [] }

theorem u1615 : Upper (D 8) (R 8) [6,192,288,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1615 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1616 : Route 9 := (fun mask => (mask,id))

def c1616 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1616 : Upper (D 8) (R 8) [6,192,288,96,160,1] 13 := by
  apply FastRouting.sound _ _ [6,192,288,96,160,1] 13 (by decide) (choices 1) [1,8,16] r1616 c1616
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u231
  · exact u232
  · exact u233

def b1617 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 7 194 292 104 176 40 81 145 273), lower := (rows 7 194 292 104 176 40 64 128 256), losses := [] }

theorem u1617 : Upper (D 8) (R 8) [6,192,288,96,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1617 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 176 33 448 448 448), lower := (rows 35 7 28 104 176 33 64 128 256), losses := [] }

theorem u1618 : Upper (D 8) (R 8) [34,5,24,96,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1618 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 385, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 176 96 449 385 385), lower := (rows 35 7 28 104 176 96 64 128 256), losses := [] }

theorem u1619 : Upper (D 8) (R 8) [34,5,24,96,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1619 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P08
