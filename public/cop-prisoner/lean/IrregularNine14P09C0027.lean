import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0001

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 70 164 200 273 48 72 385 257), lower := (rows 35 70 164 200 273 48 72 128 256), losses := [] }

theorem u1620 : Upper (D 9) (R 9) [34,68,160,192,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1620 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1621 : Route 9 := (fun mask => (mask,id))

def c1621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1621 : Upper (D 9) (R 9) [34,68,160,192,257,16,256] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,16,256] 13 (by decide) (choices 1) [1,8] r1621 c1621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u82
  · exact u83

def b1622 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 164 200 273 288 65 152 280), lower := (rows 35 70 164 200 273 288 65 128 256), losses := [] }

theorem u1622 : Upper (D 9) (R 9) [34,68,160,192,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1622 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 70 164 200 273 288 72 145 273), lower := (rows 35 70 164 200 273 288 72 128 256), losses := [] }

theorem u1623 : Upper (D 9) (R 9) [34,68,160,192,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1623 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1624 : Route 9 := (fun mask => (mask,id))

def c1624 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1624 : Upper (D 9) (R 9) [34,68,160,192,257,256,16] 13 := by
  apply FastRouting.sound _ _ [34,68,160,192,257,256,16] 13 (by decide) (choices 1) [1,8] r1624 c1624
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u84
  · exact u85

def b1625 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 75, targets := 256 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,8),(1,8),(3,5),(3,8),(4,5)], upper := (rows 35 70 164 200 280 288 65 145 273), lower := (rows 35 70 164 200 280 288 65 128 256), losses := [] }

theorem u1625 : Upper (D 9) (R 9) [34,68,160,192,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1625 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6),(3,5),(4,5)], upper := (rows 35 70 164 200 280 288 80 129 257), lower := (rows 35 70 164 200 280 288 80 128 256), losses := [] }

theorem u1626 : Upper (D 9) (R 9) [34,68,160,192,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1626 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 164 265 336 40 65 144 400), lower := (rows 35 70 164 265 336 40 65 128 256), losses := [] }

theorem u1627 : Upper (D 9) (R 9) [34,68,160,257,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1627 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 429, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 70 164 265 336 40 80 129 385), lower := (rows 35 70 164 265 336 40 80 128 256), losses := [] }

theorem u1628 : Upper (D 9) (R 9) [34,68,160,257,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1628 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(3,5),(3,7),(4,7)], upper := (rows 35 70 164 265 336 40 192 145 273), lower := (rows 35 70 164 265 336 40 192 128 256), losses := [] }

theorem u1629 : Upper (D 9) (R 9) [34,68,160,257,320,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1629 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 35 70 164 265 400 40 65 208 336), lower := (rows 35 70 164 265 400 40 65 128 256), losses := [] }

theorem u1630 : Upper (D 9) (R 9) [34,68,160,257,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1630 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 35 70 164 265 400 40 80 193 321), lower := (rows 35 70 164 265 400 40 80 128 256), losses := [] }

theorem u1631 : Upper (D 9) (R 9) [34,68,160,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1631 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 320, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 25 176 40 65 448 320), lower := (rows 35 70 388 25 176 40 65 128 256), losses := [] }

theorem u1632 : Upper (D 9) (R 9) [34,68,384,17,160,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1632 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,8),(1,0),(3,8),(4,8)], upper := (rows 35 70 388 25 176 40 320 193 321), lower := (rows 35 70 388 25 176 40 320 128 256), losses := [] }

theorem u1633 : Upper (D 9) (R 9) [34,68,384,17,160,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1633 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 25 208 33 72 416 288), lower := (rows 35 70 388 25 208 33 72 128 256), losses := [] }

theorem u1634 : Upper (D 9) (R 9) [34,68,384,17,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1634 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 25 208 33 96 392 264), lower := (rows 35 70 388 25 208 33 96 128 256), losses := [] }

theorem u1635 : Upper (D 9) (R 9) [34,68,384,17,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1635 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 82, targets := 33 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,8),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 25 208 33 320 168 296), lower := (rows 35 70 388 25 208 33 320 128 256), losses := [] }

theorem u1636 : Upper (D 9) (R 9) [34,68,384,17,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1636 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 25 208 40 65 416 288), lower := (rows 35 70 388 25 208 40 65 128 256), losses := [] }

theorem u1637 : Upper (D 9) (R 9) [34,68,384,17,192,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1637 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 25 208 40 96 385 257), lower := (rows 35 70 388 25 208 40 96 128 256), losses := [] }

theorem u1638 : Upper (D 9) (R 9) [34,68,384,17,192,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1638 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 25 208 40 320 161 289), lower := (rows 35 70 388 25 208 40 320 128 256), losses := [] }

theorem u1639 : Upper (D 9) (R 9) [34,68,384,17,192,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1639 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 },{ cop := 3, region := 388, targets := 1 }], pairs := [(0,8),(1,8),(2,0),(3,8),(4,8)], upper := (rows 35 70 388 56 208 33 65 392 264), lower := (rows 35 70 388 56 208 33 65 128 256), losses := [] }

theorem u1640 : Upper (D 9) (R 9) [34,68,384,48,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1640 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 56 208 33 72 385 257), lower := (rows 35 70 388 56 208 33 72 128 256), losses := [] }

theorem u1641 : Upper (D 9) (R 9) [34,68,384,48,192,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1641 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,8),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 56 208 33 320 137 265), lower := (rows 35 70 388 56 208 33 320 128 256), losses := [] }

theorem u1642 : Upper (D 9) (R 9) [34,68,384,48,192,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1642 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 216, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,6),(0,7),(1,7),(3,8),(4,8)], upper := (rows 35 70 388 56 208 288 65 137 265), lower := (rows 35 70 388 56 208 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 16 292 0 128 256), good := (rows 35 39 420 56 144 288 1 128 288) }] }

theorem u1643 : Upper (D 9) (R 9) [34,68,384,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1643 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 122, targets := 1 },{ cop := 0, region := 216, targets := 256 }], pairs := [(1,0),(3,0),(3,8),(4,0)], upper := (rows 35 70 388 56 208 288 72 129 257), lower := (rows 35 70 388 56 208 288 72 128 256), losses := [] }

theorem u1644 : Upper (D 9) (R 9) [34,68,384,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1644 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 35 70 388 73 145 48 72 416 288), lower := (rows 35 70 388 73 145 48 72 128 256), losses := [] }

theorem u1645 : Upper (D 9) (R 9) [34,68,384,65,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1645 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 73 145 48 96 392 264), lower := (rows 35 70 388 73 145 48 96 128 256), losses := [] }

theorem u1646 : Upper (D 9) (R 9) [34,68,384,65,129,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1646 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,8),(1,0),(3,8),(4,8)], upper := (rows 35 70 388 73 145 48 320 168 296), lower := (rows 35 70 388 73 145 48 320 128 256), losses := [] }

theorem u1647 : Upper (D 9) (R 9) [34,68,384,65,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1647 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 73 152 48 65 416 288), lower := (rows 35 70 388 73 152 48 65 128 256), losses := [] }

theorem u1648 : Upper (D 9) (R 9) [34,68,384,65,136,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1648 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 73 152 48 96 385 257), lower := (rows 35 70 388 73 152 48 96 128 256), losses := [] }

theorem u1649 : Upper (D 9) (R 9) [34,68,384,65,136,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1649 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,8),(1,0),(3,8),(4,8)], upper := (rows 35 70 388 73 152 48 320 161 289), lower := (rows 35 70 388 73 152 48 320 128 256), losses := [] }

theorem u1650 : Upper (D 9) (R 9) [34,68,384,65,136,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1650 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 88 145 40 65 416 288), lower := (rows 35 70 388 88 145 40 65 128 256), losses := [] }

theorem u1651 : Upper (D 9) (R 9) [34,68,384,80,129,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1651 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 404, targets := 96 }], pairs := [(2,5),(2,6),(4,5),(4,6)], upper := (rows 35 70 388 88 145 40 96 385 257), lower := (rows 35 70 388 88 145 40 96 128 256), losses := [] }

theorem u1652 : Upper (D 9) (R 9) [34,68,384,80,129,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1652 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,8),(1,0),(3,8),(4,8)], upper := (rows 35 70 388 88 145 40 320 161 289), lower := (rows 35 70 388 88 145 40 320 128 256), losses := [] }

theorem u1653 : Upper (D 9) (R 9) [34,68,384,80,129,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1653 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 },{ cop := 3, region := 390, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 88 176 33 65 392 264), lower := (rows 35 70 388 88 176 33 65 128 256), losses := [] }

theorem u1654 : Upper (D 9) (R 9) [34,68,384,80,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1654 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 88 176 33 72 385 257), lower := (rows 35 70 388 88 176 33 72 128 256), losses := [] }

theorem u1655 : Upper (D 9) (R 9) [34,68,384,80,160,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1655 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 1, region := 33, targets := 192 }], pairs := [(0,6),(0,7),(0,8),(3,8),(4,8)], upper := (rows 35 70 388 88 176 33 320 137 265), lower := (rows 35 70 388 88 176 33 320 128 256), losses := [] }

theorem u1656 : Upper (D 9) (R 9) [34,68,384,80,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1656 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8),(4,8)], upper := (rows 35 70 388 104 145 48 65 392 264), lower := (rows 35 70 388 104 145 48 65 128 256), losses := [] }

theorem u1657 : Upper (D 9) (R 9) [34,68,384,96,129,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1657 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 123, targets := 256 }], pairs := [(0,8),(1,8),(3,8)], upper := (rows 35 70 388 104 145 48 72 385 257), lower := (rows 35 70 388 104 145 48 72 128 256), losses := [] }

theorem u1658 : Upper (D 9) (R 9) [34,68,384,96,129,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1658 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 185, targets := 256 },{ cop := 2, region := 66, targets := 1 }], pairs := [(0,8),(1,0),(3,8),(4,8)], upper := (rows 35 70 388 104 145 48 320 137 265), lower := (rows 35 70 388 104 145 48 320 128 256), losses := [] }

theorem u1659 : Upper (D 9) (R 9) [34,68,384,96,129,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1659 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 169, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(3,8),(4,7)], upper := (rows 35 70 388 137 273 40 80 224 352), lower := (rows 35 70 388 137 273 40 80 128 256), losses := [] }

theorem u1660 : Upper (D 9) (R 9) [34,68,384,129,257,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1660 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(1,8),(3,8),(4,7)], upper := (rows 35 70 388 137 273 40 96 208 336), lower := (rows 35 70 388 137 273 40 96 128 256), losses := [] }

theorem u1661 : Upper (D 9) (R 9) [34,68,384,129,257,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1661 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 96, camps := [{ cop := 1, region := 169, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(3,8)], upper := (rows 35 70 388 137 280 33 80 224 352), lower := (rows 35 70 388 137 280 33 80 128 256), losses := [] }

theorem u1662 : Upper (D 9) (R 9) [34,68,384,129,264,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1662 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,8)], upper := (rows 35 70 388 137 280 33 96 208 336), lower := (rows 35 70 388 137 280 33 96 128 256), losses := [] }

theorem u1663 : Upper (D 9) (R 9) [34,68,384,129,264,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1663 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1664 : Route 9 := (fun mask => (mask,id))

def c1664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1664 : Upper (D 9) (R 9) [34,68,384,129,264,16,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264,16,1] 13 (by decide) (choices 1) [32,64] r1664 c1664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u86
  · exact u87

def r1665 : Route 9 := (fun mask => (mask,id))

def c1665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1665 : Upper (D 9) (R 9) [34,68,384,129,264,16,32] 13 := by
  apply FastRouting.sound _ _ [34,68,384,129,264,16,32] 13 (by decide) (choices 1) [1,64] r1665 c1665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u88
  · exact u89

def b1666 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 70 388 137 304 33 72 208 336), lower := (rows 35 70 388 137 304 33 72 128 256), losses := [] }

theorem u1666 : Upper (D 9) (R 9) [34,68,384,129,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1666 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(4,7)], upper := (rows 35 70 388 137 304 33 80 200 328), lower := (rows 35 70 388 137 304 33 80 128 256), losses := [] }

theorem u1667 : Upper (D 9) (R 9) [34,68,384,129,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1667 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(1,8),(3,8),(4,7)], upper := (rows 35 70 388 137 304 40 65 208 336), lower := (rows 35 70 388 137 304 40 65 128 256), losses := [] }

theorem u1668 : Upper (D 9) (R 9) [34,68,384,129,288,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1668 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 169, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(3,8),(4,7)], upper := (rows 35 70 388 137 304 40 80 193 321), lower := (rows 35 70 388 137 304 40 80 128 256), losses := [] }

theorem u1669 : Upper (D 9) (R 9) [34,68,384,129,288,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1669 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 70 388 137 336 33 72 176 304), lower := (rows 35 70 388 137 336 33 72 128 256), losses := [] }

theorem u1670 : Upper (D 9) (R 9) [34,68,384,129,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1670 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 137 336 33 80 168 296), lower := (rows 35 70 388 137 336 33 80 128 256), losses := [] }

theorem u1671 : Upper (D 9) (R 9) [34,68,384,129,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1671 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 388 137 336 33 96 152 280), lower := (rows 35 70 388 137 336 33 96 128 256), losses := [] }

theorem u1672 : Upper (D 9) (R 9) [34,68,384,129,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1672 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(1,8),(3,8),(4,7)], upper := (rows 35 70 388 137 336 40 65 176 304), lower := (rows 35 70 388 137 336 40 65 128 256), losses := [] }

theorem u1673 : Upper (D 9) (R 9) [34,68,384,129,320,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1673 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 82, targets := 161 }], pairs := [(1,0),(1,5),(1,7)], upper := (rows 35 70 388 137 336 40 80 161 289), lower := (rows 35 70 388 137 336 40 80 128 256), losses := [] }

theorem u1674 : Upper (D 9) (R 9) [34,68,384,129,320,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1674 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 0, region := 336, targets := 128 }], pairs := [(0,8),(1,8),(3,8),(4,7)], upper := (rows 35 70 388 137 336 40 96 145 273), lower := (rows 35 70 388 137 336 40 96 128 256), losses := [] }

theorem u1675 : Upper (D 9) (R 9) [34,68,384,129,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1675 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 388 152 304 33 65 200 328), lower := (rows 35 70 388 152 304 33 65 128 256), losses := [] }

theorem u1676 : Upper (D 9) (R 9) [34,68,384,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1676 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 65, camps := [{ cop := 1, region := 305, targets := 128 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(4,7)], upper := (rows 35 70 388 152 304 33 72 193 321), lower := (rows 35 70 388 152 304 33 72 128 256), losses := [] }

theorem u1677 : Upper (D 9) (R 9) [34,68,384,144,288,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1677 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 388 152 336 33 65 168 296), lower := (rows 35 70 388 152 336 33 65 128 256), losses := [] }

theorem u1678 : Upper (D 9) (R 9) [34,68,384,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1678 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 90, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 70 388 152 336 33 72 161 289), lower := (rows 35 70 388 152 336 33 72 128 256), losses := [] }

theorem u1679 : Upper (D 9) (R 9) [34,68,384,144,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1679 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P09
