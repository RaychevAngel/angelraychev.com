import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0009
import IrregularNine14P10C0010

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1620 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 152 273 352 352 480 352), lower := (rows 7 74 164 152 273 32 64 128 256), losses := [] }

theorem u1620 : Upper (D 10) (R 10) [6,72,160,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1620 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1621 : Route 9 := (fun mask => (mask,id))

def c1621 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1621 : Upper (D 10) (R 10) [6,72,160,144,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,144,288] 13 (by decide) (choices 1) [1,64,256] r1621 c1621
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u559
  · exact u560
  · exact u561

def b1622 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 152 336 289 353 417 289), lower := (rows 7 74 164 152 336 32 64 128 256), losses := [] }

theorem u1622 : Upper (D 10) (R 10) [6,72,160,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1622 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1623 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 49 368 336 464 336), lower := (rows 7 74 164 168 49 32 64 128 256), losses := [] }

theorem u1623 : Upper (D 10) (R 10) [6,72,160,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1623 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1624 : PairBound 9 := { available := 273, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 112 305 337 401 273), lower := (rows 7 74 164 168 112 32 64 128 256), losses := [] }

theorem u1624 : Upper (D 10) (R 10) [6,72,160,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1624 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1625 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 273 368 368 496 368), lower := (rows 7 74 164 168 273 32 64 128 256), losses := [] }

theorem u1625 : Upper (D 10) (R 10) [6,72,160,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1625 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1626 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 304 369 337 465 337), lower := (rows 7 74 164 168 304 32 64 128 256), losses := [] }

theorem u1626 : Upper (D 10) (R 10) [6,72,160,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1626 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1627 : PairBound 9 := { available := 305, camps := [{ cop := 2, region := 8, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 168 336 305 369 433 305), lower := (rows 7 74 164 168 336 32 64 128 256), losses := [] }

theorem u1627 : Upper (D 10) (R 10) [6,72,160,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1627 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1628 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 200 49 304 368 432 304), lower := (rows 7 74 164 200 49 32 64 128 256), losses := [] }

theorem u1628 : Upper (D 10) (R 10) [6,72,160,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1628 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1629 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 200 273 304 368 432 304), lower := (rows 7 74 164 200 273 32 64 128 256), losses := [] }

theorem u1629 : Upper (D 10) (R 10) [6,72,160,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1629 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1630 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 200 304 305 369 433 305), lower := (rows 7 74 164 200 304 32 64 128 256), losses := [] }

theorem u1630 : Upper (D 10) (R 10) [6,72,160,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1630 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1631 : Route 9 := (fun mask => (mask,id))

def c1631 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1631 : Upper (D 10) (R 10) [6,72,160,257,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,96] 13 (by decide) (choices 1) [16,128,256] r1631 c1631
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u562
  · exact u563
  · exact u564

def b1632 : PairBound 9 := { available := 368, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 74 164 265 176 368 368 496 368), lower := (rows 7 74 164 265 176 32 64 128 256), losses := [] }

theorem u1632 : Upper (D 10) (R 10) [6,72,160,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1632 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1633 : Route 9 := (fun mask => (mask,id))

def c1633 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1633 : Upper (D 10) (R 10) [6,72,160,257,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,192] 13 (by decide) (choices 1) [16,256] r1633 c1633
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u565
  · exact u566

def r1634 : Route 9 := (fun mask => (mask,id))

def c1634 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1634 : Upper (D 10) (R 10) [6,72,160,257,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,288] 13 (by decide) (choices 1) [16,64,128] r1634 c1634
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u567
  · exact u568
  · exact u569

def b1635 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 164, targets := 64 },{ cop := 4, region := 164, targets := 256 }], pairs := [(2,6),(2,8)], upper := (rows 7 74 164 265 336 176 240 176 432), lower := (rows 7 74 164 265 336 32 64 128 256), losses := [] }

theorem u1635 : Upper (D 10) (R 10) [6,72,160,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1635 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1636 : Route 9 := (fun mask => (mask,id))

def c1636 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1636 : Upper (D 10) (R 10) [6,72,160,257,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,257,384] 13 (by decide) (choices 1) [16,64] r1636 c1636
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u570
  · exact u571

def r1637 : Route 9 := (fun mask => (mask,id))

def c1637 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1637 : Upper (D 10) (R 10) [6,72,160,272,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,272,33] 13 (by decide) (choices 1) [64,128,256] r1637 c1637
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u572
  · exact u573
  · exact u574

def b1638 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 280 81 416 480 416 416), lower := (rows 7 74 164 280 81 32 64 128 256), losses := [] }

theorem u1638 : Upper (D 10) (R 10) [6,72,160,272,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1638 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1639 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 280 112 417 481 417 417), lower := (rows 7 74 164 280 112 32 64 128 256), losses := [] }

theorem u1639 : Upper (D 10) (R 10) [6,72,160,272,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1639 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1640 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 74 164 280 145 352 352 480 352), lower := (rows 7 74 164 280 145 32 64 128 256), losses := [] }

theorem u1640 : Upper (D 10) (R 10) [6,72,160,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1640 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1641 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 74 164 280 176 353 353 481 353), lower := (rows 7 74 164 280 176 32 64 128 256), losses := [] }

theorem u1641 : Upper (D 10) (R 10) [6,72,160,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1641 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1642 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 280 208 289 353 417 289), lower := (rows 7 74 164 280 208 32 64 128 256), losses := [] }

theorem u1642 : Upper (D 10) (R 10) [6,72,160,272,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1642 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1643 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 280 273 224 224 224 480), lower := (rows 7 74 164 280 273 32 64 128 256), losses := [] }

theorem u1643 : Upper (D 10) (R 10) [6,72,160,272,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1643 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1644 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 280 304 225 225 225 481), lower := (rows 7 74 164 280 304 32 64 128 256), losses := [] }

theorem u1644 : Upper (D 10) (R 10) [6,72,160,272,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1644 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1645 : PairBound 9 := { available := 161, camps := [{ cop := 4, region := 10, targets := 160 }], pairs := [(1,5),(1,7)], upper := (rows 7 74 164 280 336 161 225 161 417), lower := (rows 7 74 164 280 336 32 64 128 256), losses := [] }

theorem u1645 : Upper (D 10) (R 10) [6,72,160,272,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1645 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1646 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 231, targets := 256 }], pairs := [(0,8),(1,8)], upper := (rows 7 74 164 280 400 97 97 225 353), lower := (rows 7 74 164 280 400 32 64 128 256), losses := [] }

theorem u1646 : Upper (D 10) (R 10) [6,72,160,272,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1646 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1647 : Route 9 := (fun mask => (mask,id))

def c1647 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1647 : Upper (D 10) (R 10) [6,72,160,288,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,33] 13 (by decide) (choices 1) [16,64,128,256] r1647 c1647
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u575
  · exact u576
  · exact u577
  · exact u578

def b1648 : PairBound 9 := { available := 432, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 164 296 81 432 496 432 432), lower := (rows 7 74 164 296 81 32 64 128 256), losses := [] }

theorem u1648 : Upper (D 10) (R 10) [6,72,160,288,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1648 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1649 : Route 9 := (fun mask => (mask,id))

def c1649 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1649 : Upper (D 10) (R 10) [6,72,160,288,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,96] 13 (by decide) (choices 1) [1,16,128,256] r1649 c1649
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u579
  · exact u580
  · exact u581
  · exact u582

def b1650 : PairBound 9 := { available := 368, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 74 164 296 145 368 368 496 368), lower := (rows 7 74 164 296 145 32 64 128 256), losses := [] }

theorem u1650 : Upper (D 10) (R 10) [6,72,160,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1650 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1651 : PairBound 9 := { available := 337, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 74 164 296 176 369 337 465 337), lower := (rows 7 74 164 296 176 32 64 128 256), losses := [] }

theorem u1651 : Upper (D 10) (R 10) [6,72,160,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1651 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1652 : Route 9 := (fun mask => (mask,id))

def c1652 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1652 : Upper (D 10) (R 10) [6,72,160,288,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,192] 13 (by decide) (choices 1) [1,16,256] r1652 c1652
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u583
  · exact u584
  · exact u585

def r1653 : Route 9 := (fun mask => (mask,id))

def c1653 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 256 => 8 | _ => 0)

theorem u1653 : Upper (D 10) (R 10) [6,72,160,288,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,257] 13 (by decide) (choices 1) [16,64,128] r1653 c1653
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u586
  · exact u587
  · exact u588

def b1654 : PairBound 9 := { available := 209, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 74 164 296 304 241 209 209 465), lower := (rows 7 74 164 296 304 32 64 128 256), losses := [] }

theorem u1654 : Upper (D 10) (R 10) [6,72,160,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1654 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1655 : Route 9 := (fun mask => (mask,id))

def c1655 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1655 : Upper (D 10) (R 10) [6,72,160,288,320] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,320] 13 (by decide) (choices 1) [1,16,128] r1655 c1655
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u589
  · exact u590
  · exact u591

def r1656 : Route 9 := (fun mask => (mask,id))

def c1656 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1656 : Upper (D 10) (R 10) [6,72,160,288,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,288,384] 13 (by decide) (choices 1) [1,16,64] r1656 c1656
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u592
  · exact u593
  · exact u594

def b1657 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 328 49 432 496 432 432), lower := (rows 7 74 164 328 49 32 64 128 256), losses := [] }

theorem u1657 : Upper (D 10) (R 10) [6,72,160,320,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1657 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1658 : PairBound 9 := { available := 176, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 328 273 176 240 176 432), lower := (rows 7 74 164 328 273 32 64 128 256), losses := [] }

theorem u1658 : Upper (D 10) (R 10) [6,72,160,320,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1658 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1659 : PairBound 9 := { available := 177, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 328 304 177 241 177 433), lower := (rows 7 74 164 328 304 32 64 128 256), losses := [] }

theorem u1659 : Upper (D 10) (R 10) [6,72,160,320,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1659 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1660 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 328 400 49 113 177 305), lower := (rows 7 74 164 328 400 32 64 128 256), losses := [] }

theorem u1660 : Upper (D 10) (R 10) [6,72,160,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1660 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1661 : Route 9 := (fun mask => (mask,id))

def c1661 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1661 : Upper (D 10) (R 10) [6,72,160,384,33] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384,33] 13 (by decide) (choices 1) [16,64,256] r1661 c1661
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u595
  · exact u596
  · exact u597

def b1662 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 164 392 81 304 368 432 304), lower := (rows 7 74 164 392 81 32 64 128 256), losses := [] }

theorem u1662 : Upper (D 10) (R 10) [6,72,160,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1662 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1663 : Route 9 := (fun mask => (mask,id))

def c1663 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1663 : Upper (D 10) (R 10) [6,72,160,384,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384,96] 13 (by decide) (choices 1) [1,16,256] r1663 c1663
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u598
  · exact u599
  · exact u600

def b1664 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 4, region := 228, targets := 256 }], pairs := [(2,8),(4,7)], upper := (rows 7 74 164 392 273 112 112 240 368), lower := (rows 7 74 164 392 273 32 64 128 256), losses := [] }

theorem u1664 : Upper (D 10) (R 10) [6,72,160,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1664 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1665 : Route 9 := (fun mask => (mask,id))

def c1665 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1665 : Upper (D 10) (R 10) [6,72,160,384,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384,288] 13 (by decide) (choices 1) [1,16,64] r1665 c1665
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u601
  · exact u602
  · exact u603

def r1666 : Route 9 := (fun mask => (mask,id))

def c1666 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1666 : Upper (D 10) (R 10) [6,72,160,384,320] 13 := by
  apply FastRouting.sound _ _ [6,72,160,384,320] 13 (by decide) (choices 1) [1,16] r1666 c1666
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u604
  · exact u605

def b1667 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 41 176 304 368 432 304), lower := (rows 7 74 196 41 176 32 64 128 256), losses := [] }

theorem u1667 : Upper (D 10) (R 10) [6,72,192,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1667 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1668 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 41 304 432 496 432 432), lower := (rows 7 74 196 41 304 32 64 128 256), losses := [] }

theorem u1668 : Upper (D 10) (R 10) [6,72,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1668 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1669 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 41 400 304 368 432 304), lower := (rows 7 74 196 41 400 32 64 128 256), losses := [] }

theorem u1669 : Upper (D 10) (R 10) [6,72,192,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1669 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1670 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 56 145 288 352 416 288), lower := (rows 7 74 196 56 145 32 64 128 256), losses := [] }

theorem u1670 : Upper (D 10) (R 10) [6,72,192,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1670 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1671 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 56 273 416 480 416 416), lower := (rows 7 74 196 56 273 32 64 128 256), losses := [] }

theorem u1671 : Upper (D 10) (R 10) [6,72,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1671 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1672 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 56 400 289 353 417 289), lower := (rows 7 74 196 56 400 32 64 128 256), losses := [] }

theorem u1672 : Upper (D 10) (R 10) [6,72,192,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1672 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1673 : PairBound 9 := { available := 304, camps := [{ cop := 2, region := 11, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 74 196 137 304 304 368 432 304), lower := (rows 7 74 196 137 304 32 64 128 256), losses := [] }

theorem u1673 : Upper (D 10) (R 10) [6,72,192,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1673 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1674 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 152 49 288 352 416 288), lower := (rows 7 74 196 152 49 32 64 128 256), losses := [] }

theorem u1674 : Upper (D 10) (R 10) [6,72,192,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1674 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1675 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 152 273 288 352 416 288), lower := (rows 7 74 196 152 273 32 64 128 256), losses := [] }

theorem u1675 : Upper (D 10) (R 10) [6,72,192,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1675 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1676 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 152 304 289 353 417 289), lower := (rows 7 74 196 152 304 32 64 128 256), losses := [] }

theorem u1676 : Upper (D 10) (R 10) [6,72,192,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1676 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1677 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 168 49 304 368 432 304), lower := (rows 7 74 196 168 49 32 64 128 256), losses := [] }

theorem u1677 : Upper (D 10) (R 10) [6,72,192,160,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1677 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1678 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 168 273 304 368 432 304), lower := (rows 7 74 196 168 273 32 64 128 256), losses := [] }

theorem u1678 : Upper (D 10) (R 10) [6,72,192,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1678 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1679 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 168 304 305 369 433 305), lower := (rows 7 74 196 168 304 32 64 128 256), losses := [] }

theorem u1679 : Upper (D 10) (R 10) [6,72,192,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1679 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1679
end Delivery.IrregularNine14.P10
