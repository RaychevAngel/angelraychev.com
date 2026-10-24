import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P07C0001

namespace Delivery.IrregularNine14.P07
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 266 112 160 192 145 273), lower := (rows 7 42 69 266 112 160 192 128 256), losses := [] }

theorem u1620 : Upper (D 7) (R 7) [6,40,65,258,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1620 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1621 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 266 176 96 65 144 400), lower := (rows 7 42 69 266 176 96 65 128 256), losses := [] }

theorem u1621 : Upper (D 7) (R 7) [6,40,65,258,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1621 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1622 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 392, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 69 266 176 96 80 129 385), lower := (rows 7 42 69 266 176 96 80 128 256), losses := [] }

theorem u1622 : Upper (D 7) (R 7) [6,40,65,258,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1622 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1623 : Route 9 := (fun mask => (mask,id))

def c1623 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1623 : Upper (D 7) (R 7) [6,40,65,258,160,64,128] 13 := by
  apply FastRouting.sound _ _ [6,40,65,258,160,64,128] 13 (by decide) (choices 1) [1,16] r1623 c1623
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u60
  · exact u61

def b1624 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 266 208 48 65 160 416), lower := (rows 7 42 69 266 208 48 65 128 256), losses := [] }

theorem u1624 : Upper (D 7) (R 7) [6,40,65,258,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1624 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 0, region := 392, targets := 32 }], pairs := [(2,1),(3,5),(4,1)], upper := (rows 7 42 69 266 208 48 96 129 385), lower := (rows 7 42 69 266 208 48 96 128 256), losses := [] }

theorem u1625 : Upper (D 7) (R 7) [6,40,65,258,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1625 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7)], upper := (rows 7 42 69 266 208 48 192 161 289), lower := (rows 7 42 69 266 208 48 192 128 256), losses := [] }

theorem u1626 : Upper (D 7) (R 7) [6,40,65,258,192,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1626 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 266 208 160 65 176 304), lower := (rows 7 42 69 266 208 160 65 128 256), losses := [] }

theorem u1627 : Upper (D 7) (R 7) [6,40,65,258,192,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1627 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 69 266 208 160 80 161 289), lower := (rows 7 42 69 266 208 160 80 128 256), losses := [] }

theorem u1628 : Upper (D 7) (R 7) [6,40,65,258,192,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1628 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,1),(2,7),(4,1)], upper := (rows 7 42 69 266 208 160 96 145 273), lower := (rows 7 42 69 266 208 160 96 128 256), losses := [] }

theorem u1629 : Upper (D 7) (R 7) [6,40,65,258,192,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1629 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 280 112 160 65 130 386), lower := (rows 7 42 69 280 112 160 65 128 256), losses := [] }

theorem u1630 : Upper (D 7) (R 7) [6,40,65,272,96,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1630 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1631 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(2,7),(4,7)], upper := (rows 7 42 69 280 112 160 66 129 385), lower := (rows 7 42 69 280 112 160 66 128 256), losses := [] }

theorem u1631 : Upper (D 7) (R 7) [6,40,65,272,96,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1631 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1632 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 280 112 160 192 131 259), lower := (rows 7 42 69 280 112 160 192 128 256), losses := [] }

theorem u1632 : Upper (D 7) (R 7) [6,40,65,272,96,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1632 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1633 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 280 146 96 65 160 416), lower := (rows 7 42 69 280 146 96 65 128 256), losses := [] }

theorem u1633 : Upper (D 7) (R 7) [6,40,65,272,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1633 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1634 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 280 146 96 96 129 385), lower := (rows 7 42 69 280 146 96 96 128 256), losses := [] }

theorem u1634 : Upper (D 7) (R 7) [6,40,65,272,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1634 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1635 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(0,5),(1,0),(2,1),(2,5)], upper := (rows 7 42 69 280 146 96 192 161 289), lower := (rows 7 42 69 280 146 96 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 252 208 128 256), good := (rows 38 42 100 378 242 96 224 224 256) }] }

theorem u1635 : Upper (D 7) (R 7) [6,40,65,272,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1635 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1636 : PairBound 9 := { available := 130, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 280 176 96 65 130 386), lower := (rows 7 42 69 280 176 96 65 128 256), losses := [] }

theorem u1636 : Upper (D 7) (R 7) [6,40,65,272,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1636 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1637 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 42 69 280 176 96 66 129 385), lower := (rows 7 42 69 280 176 96 66 128 256), losses := [] }

theorem u1637 : Upper (D 7) (R 7) [6,40,65,272,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1637 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1638 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 6, region := 48, targets := 3 }], pairs := [(0,5),(2,5),(4,0),(4,1)], upper := (rows 7 42 69 280 176 96 192 131 259), lower := (rows 7 42 69 280 176 96 192 128 256), losses := [] }

theorem u1638 : Upper (D 7) (R 7) [6,40,65,272,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1638 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 280 208 33 66 160 416), lower := (rows 7 42 69 280 208 33 66 128 256), losses := [] }

theorem u1639 : Upper (D 7) (R 7) [6,40,65,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1639 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 280 208 33 96 130 386), lower := (rows 7 42 69 280 208 33 96 128 256), losses := [] }

theorem u1640 : Upper (D 7) (R 7) [6,40,65,272,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1640 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 280 208 33 192 162 290), lower := (rows 7 42 69 280 208 33 192 128 256), losses := [] }

theorem u1641 : Upper (D 7) (R 7) [6,40,65,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1641 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 280 208 34 65 160 416), lower := (rows 7 42 69 280 208 34 65 128 256), losses := [] }

theorem u1642 : Upper (D 7) (R 7) [6,40,65,272,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1642 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 69 280 208 34 96 129 385), lower := (rows 7 42 69 280 208 34 96 128 256), losses := [] }

theorem u1643 : Upper (D 7) (R 7) [6,40,65,272,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1643 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 69 280 208 34 192 161 289), lower := (rows 7 42 69 280 208 34 192 128 256), losses := [] }

theorem u1644 : Upper (D 7) (R 7) [6,40,65,272,192,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1644 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 328 49 160 66 144 400), lower := (rows 7 42 69 328 49 160 66 128 256), losses := [] }

theorem u1645 : Upper (D 7) (R 7) [6,40,65,320,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1645 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 69 328 49 160 80 130 386), lower := (rows 7 42 69 328 49 160 80 128 256), losses := [] }

theorem u1646 : Upper (D 7) (R 7) [6,40,65,320,33,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1646 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1647 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 458, targets := 1 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(2,1),(3,0),(4,6)], upper := (rows 7 42 69 328 49 160 192 146 274), lower := (rows 7 42 69 328 49 160 192 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 20 224 224 128 256), good := (rows 21 104 117 360 117 224 224 224 256) }] }

theorem u1647 : Upper (D 7) (R 7) [6,40,65,320,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1647 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1648 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 328 145 160 66 176 304), lower := (rows 7 42 69 328 145 160 66 128 256), losses := [] }

theorem u1648 : Upper (D 7) (R 7) [6,40,65,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1648 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1649 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 4, region := 68, targets := 32 }], pairs := [(1,0),(2,5),(3,0)], upper := (rows 7 42 69 328 145 160 80 162 290), lower := (rows 7 42 69 328 145 160 80 128 256), losses := [] }

theorem u1649 : Upper (D 7) (R 7) [6,40,65,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1649 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1650 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 4, region := 362, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,0)], upper := (rows 7 42 69 328 145 160 96 146 274), lower := (rows 7 42 69 328 145 160 96 128 256), losses := [] }

theorem u1650 : Upper (D 7) (R 7) [6,40,65,320,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1650 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 328 146 48 65 160 416), lower := (rows 7 42 69 328 146 48 65 128 256), losses := [] }

theorem u1651 : Upper (D 7) (R 7) [6,40,65,320,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1651 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1652 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 2, region := 392, targets := 2 }], pairs := [(0,7),(2,7),(3,1)], upper := (rows 7 42 69 328 146 48 96 129 385), lower := (rows 7 42 69 328 146 48 96 128 256), losses := [] }

theorem u1652 : Upper (D 7) (R 7) [6,40,65,320,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1652 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1653 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(0,5),(2,5),(4,6)], upper := (rows 7 42 69 328 146 48 192 161 289), lower := (rows 7 42 69 328 146 48 192 128 256), losses := [] }

theorem u1653 : Upper (D 7) (R 7) [6,40,65,320,130,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1653 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1654 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 69 328 146 160 65 176 304), lower := (rows 7 42 69 328 146 160 65 128 256), losses := [] }

theorem u1654 : Upper (D 7) (R 7) [6,40,65,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1654 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1655 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 328 146 160 80 161 289), lower := (rows 7 42 69 328 146 160 80 128 256), losses := [] }

theorem u1655 : Upper (D 7) (R 7) [6,40,65,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1655 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1656 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 69, targets := 128 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(0,7),(2,7),(4,5),(4,6)], upper := (rows 7 42 69 328 146 160 96 145 273), lower := (rows 7 42 69 328 146 160 96 128 256), losses := [] }

theorem u1656 : Upper (D 7) (R 7) [6,40,65,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1656 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1657 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 42 69 392 145 96 66 176 304), lower := (rows 7 42 69 392 145 96 66 128 256), losses := [] }

theorem u1657 : Upper (D 7) (R 7) [6,40,65,384,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1657 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 69 392 145 96 80 162 290), lower := (rows 7 42 69 392 145 96 80 128 256), losses := [] }

theorem u1658 : Upper (D 7) (R 7) [6,40,65,384,129,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1658 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 392 145 96 96 146 274), lower := (rows 7 42 69 392 145 96 96 128 256), losses := [] }

theorem u1659 : Upper (D 7) (R 7) [6,40,65,384,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1659 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 48, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 392 146 96 65 176 304), lower := (rows 7 42 69 392 146 96 65 128 256), losses := [] }

theorem u1660 : Upper (D 7) (R 7) [6,40,65,384,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1660 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1661 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 114, targets := 1 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(1,0),(4,0)], upper := (rows 7 42 69 392 146 96 80 161 289), lower := (rows 7 42 69 392 146 96 80 128 256), losses := [] }

theorem u1661 : Upper (D 7) (R 7) [6,40,65,384,130,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1661 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1662 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 69 392 146 96 96 145 273), lower := (rows 7 42 69 392 146 96 96 128 256), losses := [] }

theorem u1662 : Upper (D 7) (R 7) [6,40,65,384,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1662 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1663 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 392 176 33 66 208 336), lower := (rows 7 42 69 392 176 33 66 128 256), losses := [] }

theorem u1663 : Upper (D 7) (R 7) [6,40,65,384,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1663 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1664 : PairBound 9 := { available := 66, camps := [{ cop := 5, region := 474, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 7 42 69 392 176 33 80 194 322), lower := (rows 7 42 69 392 176 33 80 128 256), losses := [] }

theorem u1664 : Upper (D 7) (R 7) [6,40,65,384,160,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1664 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1665 : PairBound 9 := { available := 18, camps := [{ cop := 5, region := 410, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 392 176 96 65 146 274), lower := (rows 7 42 69 392 176 96 65 128 256), losses := [] }

theorem u1665 : Upper (D 7) (R 7) [6,40,65,384,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1665 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1666 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5),(0,7),(1,7),(2,7)], upper := (rows 7 42 69 392 176 96 66 145 273), lower := (rows 7 42 69 392 176 96 66 128 256), losses := [] }

theorem u1666 : Upper (D 7) (R 7) [6,40,65,384,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1666 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1667 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 3, region := 114, targets := 1 }], pairs := [(1,0),(3,5),(3,6)], upper := (rows 7 42 69 392 176 96 80 131 259), lower := (rows 7 42 69 392 176 96 80 128 256), losses := [] }

theorem u1667 : Upper (D 7) (R 7) [6,40,65,384,160,64,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1667 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 392 208 33 66 176 304), lower := (rows 7 42 69 392 208 33 66 128 256), losses := [] }

theorem u1668 : Upper (D 7) (R 7) [6,40,65,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1668 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 69 392 208 33 80 162 290), lower := (rows 7 42 69 392 208 33 80 128 256), losses := [] }

theorem u1669 : Upper (D 7) (R 7) [6,40,65,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1669 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 5, region := 474, targets := 1 }], pairs := [(0,7),(1,0),(1,7),(2,7)], upper := (rows 7 42 69 392 208 33 96 146 274), lower := (rows 7 42 69 392 208 33 96 128 256), losses := [] }

theorem u1670 : Upper (D 7) (R 7) [6,40,65,384,192,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1670 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 48, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 69 392 208 34 65 176 304), lower := (rows 7 42 69 392 208 34 65 128 256), losses := [] }

theorem u1671 : Upper (D 7) (R 7) [6,40,65,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1671 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 427, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 69 392 208 34 80 161 289), lower := (rows 7 42 69 392 208 34 80 128 256), losses := [] }

theorem u1672 : Upper (D 7) (R 7) [6,40,65,384,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1672 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 408, targets := 34 }], pairs := [(3,1),(3,5),(4,1),(4,5)], upper := (rows 7 42 69 392 208 34 96 145 273), lower := (rows 7 42 69 392 208 34 96 128 256), losses := [] }

theorem u1673 : Upper (D 7) (R 7) [6,40,65,384,192,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1673 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 298, targets := 65 }], pairs := [(1,0),(1,6),(3,0)], upper := (rows 7 42 69 392 208 48 65 162 290), lower := (rows 7 42 69 392 208 48 65 128 256), losses := [] }

theorem u1674 : Upper (D 7) (R 7) [6,40,65,384,192,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1674 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 33, camps := [{ cop := 6, region := 5, targets := 160 }], pairs := [(0,5),(0,7),(2,5)], upper := (rows 7 42 69 392 208 48 66 161 289), lower := (rows 7 42 69 392 208 48 66 128 256), losses := [] }

theorem u1675 : Upper (D 7) (R 7) [6,40,65,384,192,16,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1675 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 392, targets := 96 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(3,6)], upper := (rows 7 42 69 392 208 48 96 131 259), lower := (rows 7 42 69 392 208 48 96 128 256), losses := [] }

theorem u1676 : Upper (D 7) (R 7) [6,40,65,384,192,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1676 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 73 146 160 65 416 288), lower := (rows 7 42 84 73 146 160 65 128 256), losses := [] }

theorem u1677 : Upper (D 7) (R 7) [6,40,80,65,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1677 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 100, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 7 42 84 73 146 160 96 385 257), lower := (rows 7 42 84 73 146 160 96 128 256), losses := [] }

theorem u1678 : Upper (D 7) (R 7) [6,40,80,65,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1678 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 178, targets := 64 },{ cop := 0, region := 488, targets := 2 }], pairs := [(1,6),(3,1),(4,6)], upper := (rows 7 42 84 73 146 160 320 161 289), lower := (rows 7 42 84 73 146 160 320 128 256), losses := [] }

theorem u1679 : Upper (D 7) (R 7) [6,40,80,65,130,128,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1679 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P07
