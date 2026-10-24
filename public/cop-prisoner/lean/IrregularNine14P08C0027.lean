import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P08C0003
import IrregularNine14P08C0004

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 28 104 176 288 193 193 449), lower := (rows 35 7 28 104 176 288 64 128 256), losses := [] }

theorem u1620 : Upper (D 8) (R 8) [34,5,24,96,160,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1620 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 304 33 192 192 448), lower := (rows 35 7 28 104 304 33 64 128 256), losses := [] }

theorem u1621 : Upper (D 8) (R 8) [34,5,24,96,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1621 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 304 96 193 129 385), lower := (rows 35 7 28 104 304 96 64 128 256), losses := [] }

theorem u1622 : Upper (D 8) (R 8) [34,5,24,96,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1622 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1623 : Route 9 := (fun mask => (mask,id))

def c1623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1623 : Upper (D 8) (R 8) [34,5,24,96,288,128] 13 := by
  apply FastRouting.sound _ _ [34,5,24,96,288,128] 13 (by decide) (choices 1) [1,128] r1623 c1623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u234
  · exact u235

def b1624 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 400 33 224 224 480), lower := (rows 35 7 28 104 400 33 64 128 256), losses := [] }

theorem u1624 : Upper (D 8) (R 8) [34,5,24,96,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1624 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 161, camps := [{ cop := 3, region := 407, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 104 400 96 225 161 417), lower := (rows 35 7 28 104 400 96 64 128 256), losses := [] }

theorem u1625 : Upper (D 8) (R 8) [34,5,24,96,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1625 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 28 104 400 160 97 225 353), lower := (rows 35 7 28 104 400 160 64 128 256), losses := [] }

theorem u1626 : Upper (D 8) (R 8) [34,5,24,96,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1626 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 28 200 304 33 224 224 480), lower := (rows 35 7 28 200 304 33 64 128 256), losses := [] }

theorem u1627 : Upper (D 8) (R 8) [34,5,24,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1627 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 400, targets := 64 }], pairs := [(4,6)], upper := (rows 35 7 28 200 304 96 225 161 417), lower := (rows 35 7 28 200 304 96 64 128 256), losses := [] }

theorem u1628 : Upper (D 8) (R 8) [34,5,24,192,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1628 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 56 400 33 224 224 480), lower := (rows 35 7 76 56 400 33 64 128 256), losses := [] }

theorem u1629 : Upper (D 8) (R 8) [34,5,72,48,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1629 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 56 400 96 225 161 417), lower := (rows 35 7 76 56 400 96 64 128 256), losses := [] }

theorem u1630 : Upper (D 8) (R 8) [34,5,72,48,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1630 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 71, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 56 400 160 97 225 353), lower := (rows 35 7 76 56 400 160 64 128 256), losses := [] }

theorem u1631 : Upper (D 8) (R 8) [34,5,72,48,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1631 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 152 304 33 224 224 480), lower := (rows 35 7 76 152 304 33 64 128 256), losses := [] }

theorem u1632 : Upper (D 8) (R 8) [34,5,72,144,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1632 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 152 304 96 225 161 417), lower := (rows 35 7 76 152 304 96 64 128 256), losses := [] }

theorem u1633 : Upper (D 8) (R 8) [34,5,72,144,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1633 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 336, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 152 304 160 97 225 353), lower := (rows 35 7 76 152 304 160 64 128 256), losses := [] }

theorem u1634 : Upper (D 8) (R 8) [34,5,72,144,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1634 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 168 112 33 464 400 400), lower := (rows 35 7 76 168 112 33 64 128 256), losses := [] }

theorem u1635 : Upper (D 8) (R 8) [34,5,72,160,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1635 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 35 7 76 168 112 48 449 385 385), lower := (rows 35 7 76 168 112 48 64 128 256), losses := [] }

theorem u1636 : Upper (D 8) (R 8) [34,5,72,160,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1636 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 273, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 168 112 160 337 401 273), lower := (rows 35 7 76 168 112 160 64 128 256), losses := [] }

theorem u1637 : Upper (D 8) (R 8) [34,5,72,160,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1637 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 145, camps := [], pairs := [], upper := (rows 35 7 76 168 112 288 209 145 401), lower := (rows 35 7 76 168 112 288 64 128 256), losses := [] }

theorem u1638 : Upper (D 8) (R 8) [34,5,72,160,96,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1638 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 168 208 33 368 432 304), lower := (rows 35 7 76 168 208 33 64 128 256), losses := [] }

theorem u1639 : Upper (D 8) (R 8) [34,5,72,160,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1639 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 7 76 168 208 48 353 417 289), lower := (rows 35 7 76 168 208 48 64 128 256), losses := [] }

theorem u1640 : Upper (D 8) (R 8) [34,5,72,160,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1640 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 35 7 76 168 208 288 113 177 305), lower := (rows 35 7 76 168 208 288 64 128 256), losses := [] }

theorem u1641 : Upper (D 8) (R 8) [34,5,72,160,192,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1641 [(5,8)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 168 304 33 208 208 464), lower := (rows 35 7 76 168 304 33 64 128 256), losses := [] }

theorem u1642 : Upper (D 8) (R 8) [34,5,72,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1642 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 76 168 304 48 193 193 449), lower := (rows 35 7 76 168 304 48 64 128 256), losses := [] }

theorem u1643 : Upper (D 8) (R 8) [34,5,72,160,288,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1643 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 168 304 96 209 145 401), lower := (rows 35 7 76 168 304 96 64 128 256), losses := [] }

theorem u1644 : Upper (D 8) (R 8) [34,5,72,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1644 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 81, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 168 304 160 81 209 337), lower := (rows 35 7 76 168 304 160 64 128 256), losses := [] }

theorem u1645 : Upper (D 8) (R 8) [34,5,72,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1645 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 168 336 33 240 176 432), lower := (rows 35 7 76 168 336 33 64 128 256), losses := [] }

theorem u1646 : Upper (D 8) (R 8) [34,5,72,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1646 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 76 168 336 48 225 161 417), lower := (rows 35 7 76 168 336 48 64 128 256), losses := [] }

theorem u1647 : Upper (D 8) (R 8) [34,5,72,160,320,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1647 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 49, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 168 336 160 113 177 305), lower := (rows 35 7 76 168 336 160 64 128 256), losses := [] }

theorem u1648 : Upper (D 8) (R 8) [34,5,72,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1648 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 168 400 33 112 240 368), lower := (rows 35 7 76 168 400 33 64 128 256), losses := [] }

theorem u1649 : Upper (D 8) (R 8) [34,5,72,160,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1649 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 7 76 168 400 48 97 225 353), lower := (rows 35 7 76 168 400 48 64 128 256), losses := [] }

theorem u1650 : Upper (D 8) (R 8) [34,5,72,160,384,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1650 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 168 400 96 113 177 305), lower := (rows 35 7 76 168 400 96 64 128 256), losses := [] }

theorem u1651 : Upper (D 8) (R 8) [34,5,72,160,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1651 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 280 176 33 224 224 480), lower := (rows 35 7 76 280 176 33 64 128 256), losses := [] }

theorem u1652 : Upper (D 8) (R 8) [34,5,72,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1652 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 280 176 96 225 161 417), lower := (rows 35 7 76 280 176 96 64 128 256), losses := [] }

theorem u1653 : Upper (D 8) (R 8) [34,5,72,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1653 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 280 176 160 97 225 353), lower := (rows 35 7 76 280 176 160 64 128 256), losses := [] }

theorem u1654 : Upper (D 8) (R 8) [34,5,72,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1654 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 296 112 33 208 144 400), lower := (rows 35 7 76 296 112 33 64 128 256), losses := [] }

theorem u1655 : Upper (D 8) (R 8) [34,5,72,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1655 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 7 76 296 112 48 193 129 385), lower := (rows 35 7 76 296 112 48 64 128 256), losses := [] }

theorem u1656 : Upper (D 8) (R 8) [34,5,72,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1656 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1657 : Route 9 := (fun mask => (mask,id))

def c1657 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1657 : Upper (D 8) (R 8) [34,5,72,288,96,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288,96,128] 13 (by decide) (choices 1) [1,16,128] r1657 c1657
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u236
  · exact u237
  · exact u238

def b1658 : PairBound 9 := { available := 208, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 296 176 33 208 208 464), lower := (rows 35 7 76 296 176 33 64 128 256), losses := [] }

theorem u1658 : Upper (D 8) (R 8) [34,5,72,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1658 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 7 76 296 176 48 193 193 449), lower := (rows 35 7 76 296 176 48 64 128 256), losses := [] }

theorem u1659 : Upper (D 8) (R 8) [34,5,72,288,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1659 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 145, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 296 176 96 209 145 401), lower := (rows 35 7 76 296 176 96 64 128 256), losses := [] }

theorem u1660 : Upper (D 8) (R 8) [34,5,72,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1660 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 7 76 296 176 160 81 209 337), lower := (rows 35 7 76 296 176 160 64 128 256), losses := [] }

theorem u1661 : Upper (D 8) (R 8) [34,5,72,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1661 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 176, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 296 208 33 240 176 432), lower := (rows 35 7 76 296 208 33 64 128 256), losses := [] }

theorem u1662 : Upper (D 8) (R 8) [34,5,72,288,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1662 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 76 296 208 48 225 161 417), lower := (rows 35 7 76 296 208 48 64 128 256), losses := [] }

theorem u1663 : Upper (D 8) (R 8) [34,5,72,288,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1663 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def r1664 : Route 9 := (fun mask => (mask,id))

def c1664 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1664 : Upper (D 8) (R 8) [34,5,72,288,192,128] 13 := by
  apply FastRouting.sound _ _ [34,5,72,288,192,128] 13 (by decide) (choices 1) [1,16,32] r1664 c1664
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u239
  · exact u240
  · exact u241

def b1665 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 76 392 112 33 240 176 432), lower := (rows 35 7 76 392 112 33 64 128 256), losses := [] }

theorem u1665 : Upper (D 8) (R 8) [34,5,72,384,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1665 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 76 392 112 48 225 161 417), lower := (rows 35 7 76 392 112 48 64 128 256), losses := [] }

theorem u1666 : Upper (D 8) (R 8) [34,5,72,384,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1666 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 80, targets := 128 }], pairs := [(4,7)], upper := (rows 35 7 76 392 112 160 113 177 305), lower := (rows 35 7 76 392 112 160 64 128 256), losses := [] }

theorem u1667 : Upper (D 8) (R 8) [34,5,72,384,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1667 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 392 176 33 112 240 368), lower := (rows 35 7 76 392 176 33 64 128 256), losses := [] }

theorem u1668 : Upper (D 8) (R 8) [34,5,72,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1668 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 7 76 392 176 48 97 225 353), lower := (rows 35 7 76 392 176 48 64 128 256), losses := [] }

theorem u1669 : Upper (D 8) (R 8) [34,5,72,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1669 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 76 392 176 96 113 177 305), lower := (rows 35 7 76 392 176 96 64 128 256), losses := [] }

theorem u1670 : Upper (D 8) (R 8) [34,5,72,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1670 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 76 392 208 33 112 176 304), lower := (rows 35 7 76 392 208 33 64 128 256), losses := [] }

theorem u1671 : Upper (D 8) (R 8) [34,5,72,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1671 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 76 392 208 48 97 161 289), lower := (rows 35 7 76 392 208 48 64 128 256), losses := [] }

theorem u1672 : Upper (D 8) (R 8) [34,5,72,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1672 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 224, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 56 280 33 224 224 480), lower := (rows 35 7 196 56 280 33 64 128 256), losses := [] }

theorem u1673 : Upper (D 8) (R 8) [34,5,192,48,264,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1673 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 7 196 56 280 96 225 161 417), lower := (rows 35 7 196 56 280 96 64 128 256), losses := [] }

theorem u1674 : Upper (D 8) (R 8) [34,5,192,48,264,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1674 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 168, camps := [{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6)], upper := (rows 35 7 196 56 336 33 232 168 424), lower := (rows 35 7 196 56 336 33 64 128 256), losses := [] }

theorem u1675 : Upper (D 8) (R 8) [34,5,192,48,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1675 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 7 196 56 336 40 225 161 417), lower := (rows 35 7 196 56 336 40 64 128 256), losses := [] }

theorem u1676 : Upper (D 8) (R 8) [34,5,192,48,320,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1676 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 196 56 336 160 105 169 297), lower := (rows 35 7 196 56 336 160 64 128 256), losses := [] }

theorem u1677 : Upper (D 8) (R 8) [34,5,192,48,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1677 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 7 196 88 176 33 360 424 296), lower := (rows 35 7 196 88 176 33 64 128 256), losses := [] }

theorem u1678 : Upper (D 8) (R 8) [34,5,192,80,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1678 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 35 7 196 88 176 40 353 417 289), lower := (rows 35 7 196 88 176 40 64 128 256), losses := [] }

theorem u1679 : Upper (D 8) (R 8) [34,5,192,80,160,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1679 [(5,3)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P08
