import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0008
import IrregularNine14P10C0009

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1560 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 392 49 432 496 432 432), lower := (rows 7 74 100 392 49 32 64 128 256), losses := [] }

theorem u1560 : Upper (D 10) (R 10) [6,72,96,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1560 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1561 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 392 145 304 368 432 304), lower := (rows 7 74 100 392 145 32 64 128 256), losses := [] }

theorem u1561 : Upper (D 10) (R 10) [6,72,96,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1561 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1562 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 100 392 176 305 369 433 305), lower := (rows 7 74 100 392 176 32 64 128 256), losses := [] }

theorem u1562 : Upper (D 10) (R 10) [6,72,96,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1562 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1563 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 4, region := 388, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 148 41 112 416 480 416 416), lower := (rows 7 74 148 41 112 32 64 128 256), losses := [] }

theorem u1563 : Upper (D 10) (R 10) [6,72,144,33,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1563 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1564 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 148 41 176 352 352 480 352), lower := (rows 7 74 148 41 176 32 64 128 256), losses := [] }

theorem u1564 : Upper (D 10) (R 10) [6,72,144,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1564 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1565 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 148 41 208 288 352 416 288), lower := (rows 7 74 148 41 208 32 64 128 256), losses := [] }

theorem u1565 : Upper (D 10) (R 10) [6,72,144,33,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1565 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1566 : Route 9 := (fun mask => (mask,id))

def c1566 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1566 : Upper (D 10) (R 10) [6,72,144,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,33,288] 13 (by decide) (choices 1) [64,128,256] r1566 c1566
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u530
  · exact u531
  · exact u532

def b1567 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 4, region := 164, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 148 41 336 416 480 416 416), lower := (rows 7 74 148 41 336 32 64 128 256), losses := [] }

theorem u1567 : Upper (D 10) (R 10) [6,72,144,33,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1567 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1568 : PairBound 9 := { available := 352, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 148 41 400 352 352 480 352), lower := (rows 7 74 148 41 400 32 64 128 256), losses := [] }

theorem u1568 : Upper (D 10) (R 10) [6,72,144,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1568 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1569 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 73 304 416 480 416 416), lower := (rows 7 74 148 73 304 32 64 128 256), losses := [] }

theorem u1569 : Upper (D 10) (R 10) [6,72,144,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1569 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1570 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 104 273 416 480 416 416), lower := (rows 7 74 148 104 273 32 64 128 256), losses := [] }

theorem u1570 : Upper (D 10) (R 10) [6,72,144,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1570 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1571 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 104 304 417 481 417 417), lower := (rows 7 74 148 104 304 32 64 128 256), losses := [] }

theorem u1571 : Upper (D 10) (R 10) [6,72,144,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1571 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1572 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 137 112 288 352 416 288), lower := (rows 7 74 148 137 112 32 64 128 256), losses := [] }

theorem u1572 : Upper (D 10) (R 10) [6,72,144,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1572 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1573 : PairBound 9 := { available := 352, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 137 304 352 352 480 352), lower := (rows 7 74 148 137 304 32 64 128 256), losses := [] }

theorem u1573 : Upper (D 10) (R 10) [6,72,144,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1573 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1574 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 137 336 288 352 416 288), lower := (rows 7 74 148 137 336 32 64 128 256), losses := [] }

theorem u1574 : Upper (D 10) (R 10) [6,72,144,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1574 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1575 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 0, region := 368, targets := 128 }], pairs := [(3,6),(4,7)], upper := (rows 7 74 148 168 112 289 353 417 289), lower := (rows 7 74 148 168 112 32 64 128 256), losses := [] }

theorem u1575 : Upper (D 10) (R 10) [6,72,144,160,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1575 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1576 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 322, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 148 168 273 352 352 480 352), lower := (rows 7 74 148 168 273 32 64 128 256), losses := [] }

theorem u1576 : Upper (D 10) (R 10) [6,72,144,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1576 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1577 : Route 9 := (fun mask => (mask,id))

def c1577 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1577 : Upper (D 10) (R 10) [6,72,144,160,288] 13 := by
  apply FastRouting.sound _ _ [6,72,144,160,288] 13 (by decide) (choices 1) [1,64,256] r1577 c1577
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u533
  · exact u534
  · exact u535

def b1578 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 0, region := 368, targets := 128 }], pairs := [(3,6),(4,7)], upper := (rows 7 74 148 168 336 289 353 417 289), lower := (rows 7 74 148 168 336 32 64 128 256), losses := [] }

theorem u1578 : Upper (D 10) (R 10) [6,72,144,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1578 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1579 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 200 273 288 352 416 288), lower := (rows 7 74 148 200 273 32 64 128 256), losses := [] }

theorem u1579 : Upper (D 10) (R 10) [6,72,144,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1579 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1580 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 148 200 304 289 353 417 289), lower := (rows 7 74 148 200 304 32 64 128 256), losses := [] }

theorem u1580 : Upper (D 10) (R 10) [6,72,144,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1580 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1581 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 226, targets := 256 },{ cop := 4, region := 196, targets := 256 }], pairs := [(1,8),(2,8)], upper := (rows 7 74 148 265 304 224 224 224 480), lower := (rows 7 74 148 265 304 32 64 128 256), losses := [] }

theorem u1581 : Upper (D 10) (R 10) [6,72,144,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1581 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1582 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 3, region := 226, targets := 256 }], pairs := [(1,8),(3,6)], upper := (rows 7 74 148 265 336 160 224 160 416), lower := (rows 7 74 148 265 336 32 64 128 256), losses := [] }

theorem u1582 : Upper (D 10) (R 10) [6,72,144,257,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1582 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1583 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 148 265 400 96 96 224 352), lower := (rows 7 74 148 265 400 32 64 128 256), losses := [] }

theorem u1583 : Upper (D 10) (R 10) [6,72,144,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1583 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1584 : PairBound 9 := { available := 225, camps := [{ cop := 3, region := 16, targets := 192 }], pairs := [(4,6),(4,7)], upper := (rows 7 74 148 296 304 225 225 225 481), lower := (rows 7 74 148 296 304 32 64 128 256), losses := [] }

theorem u1584 : Upper (D 10) (R 10) [6,72,144,288,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1584 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1585 : Route 9 := (fun mask => (mask,id))

def c1585 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1585 : Upper (D 10) (R 10) [6,72,144,288,320] 13 := by
  apply FastRouting.sound _ _ [6,72,144,288,320] 13 (by decide) (choices 1) [1,128] r1585 c1585
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u536
  · exact u537

def b1586 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 363, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 74 148 296 400 97 97 225 353), lower := (rows 7 74 148 296 400 32 64 128 256), losses := [] }

theorem u1586 : Upper (D 10) (R 10) [6,72,144,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1586 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1587 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 424, targets := 64 },{ cop := 0, region := 368, targets := 128 }], pairs := [(3,6),(4,7)], upper := (rows 7 74 148 392 336 33 97 161 289), lower := (rows 7 74 148 392 336 32 64 128 256), losses := [] }

theorem u1587 : Upper (D 10) (R 10) [6,72,144,384,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1587 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1588 : Route 9 := (fun mask => (mask,id))

def c1588 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1588 : Upper (D 10) (R 10) [6,72,160,33,96] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,96] 13 (by decide) (choices 1) [16,128,256] r1588 c1588
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u538
  · exact u539
  · exact u540

def b1589 : PairBound 9 := { available := 336, camps := [{ cop := 2, region := 16, targets := 320 }], pairs := [(4,6),(4,8)], upper := (rows 7 74 164 41 176 368 336 464 336), lower := (rows 7 74 164 41 176 32 64 128 256), losses := [] }

theorem u1589 : Upper (D 10) (R 10) [6,72,160,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1589 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1590 : Route 9 := (fun mask => (mask,id))

def c1590 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1590 : Upper (D 10) (R 10) [6,72,160,33,192] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,192] 13 (by decide) (choices 1) [16,256] r1590 c1590
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u541
  · exact u542

def r1591 : Route 9 := (fun mask => (mask,id))

def c1591 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | _ => 0)

theorem u1591 : Upper (D 10) (R 10) [6,72,160,33,288] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,288] 13 (by decide) (choices 1) [16,64,128,256] r1591 c1591
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u543
  · exact u544
  · exact u545
  · exact u546

def r1592 : Route 9 := (fun mask => (mask,id))

def c1592 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1592 : Upper (D 10) (R 10) [6,72,160,33,320] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,320] 13 (by decide) (choices 1) [16,128,256] r1592 c1592
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u547
  · exact u548
  · exact u549

def r1593 : Route 9 := (fun mask => (mask,id))

def c1593 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1593 : Upper (D 10) (R 10) [6,72,160,33,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,33,384] 13 (by decide) (choices 1) [16,64,256] r1593 c1593
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u550
  · exact u551
  · exact u552

def b1594 : PairBound 9 := { available := 448, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 74 164 56 49 480 448 448 448), lower := (rows 7 74 164 56 49 32 64 128 256), losses := [] }

theorem u1594 : Upper (D 10) (R 10) [6,72,160,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1594 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1595 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 56 81 416 480 416 416), lower := (rows 7 74 164 56 81 32 64 128 256), losses := [] }

theorem u1595 : Upper (D 10) (R 10) [6,72,160,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1595 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1596 : PairBound 9 := { available := 385, camps := [{ cop := 4, region := 10, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 74 164 56 112 417 449 385 385), lower := (rows 7 74 164 56 112 32 64 128 256), losses := [] }

theorem u1596 : Upper (D 10) (R 10) [6,72,160,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1596 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1597 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 74 164 56 145 352 352 480 352), lower := (rows 7 74 164 56 145 32 64 128 256), losses := [] }

theorem u1597 : Upper (D 10) (R 10) [6,72,160,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1597 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1598 : PairBound 9 := { available := 321, camps := [{ cop := 2, region := 24, targets := 320 }], pairs := [(3,6),(3,8)], upper := (rows 7 74 164 56 176 353 321 449 321), lower := (rows 7 74 164 56 176 32 64 128 256), losses := [] }

theorem u1598 : Upper (D 10) (R 10) [6,72,160,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1598 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1599 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 56 208 289 353 417 289), lower := (rows 7 74 164 56 208 32 64 128 256), losses := [] }

theorem u1599 : Upper (D 10) (R 10) [6,72,160,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1599 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1600 : Route 9 := (fun mask => (mask,id))

def c1600 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | _ => 0)

theorem u1600 : Upper (D 10) (R 10) [6,72,160,48,257] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,257] 13 (by decide) (choices 1) [64,128,256] r1600 c1600
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u553
  · exact u554
  · exact u555

def b1601 : PairBound 9 := { available := 449, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 74 164 56 304 481 449 449 449), lower := (rows 7 74 164 56 304 32 64 128 256), losses := [] }

theorem u1601 : Upper (D 10) (R 10) [6,72,160,48,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1601 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1602 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 56 336 417 481 417 417), lower := (rows 7 74 164 56 336 32 64 128 256), losses := [] }

theorem u1602 : Upper (D 10) (R 10) [6,72,160,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1602 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1603 : Route 9 := (fun mask => (mask,id))

def c1603 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1603 : Upper (D 10) (R 10) [6,72,160,48,384] 13 := by
  apply FastRouting.sound _ _ [6,72,160,48,384] 13 (by decide) (choices 1) [1,64,256] r1603 c1603
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u556
  · exact u557
  · exact u558

def b1604 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 73 304 432 496 432 432), lower := (rows 7 74 164 73 304 32 64 128 256), losses := [] }

theorem u1604 : Upper (D 10) (R 10) [6,72,160,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1604 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1605 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 73 400 304 368 432 304), lower := (rows 7 74 164 73 400 32 64 128 256), losses := [] }

theorem u1605 : Upper (D 10) (R 10) [6,72,160,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1605 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1606 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 88 49 416 480 416 416), lower := (rows 7 74 164 88 49 32 64 128 256), losses := [] }

theorem u1606 : Upper (D 10) (R 10) [6,72,160,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1606 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1607 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 88 273 416 480 416 416), lower := (rows 7 74 164 88 273 32 64 128 256), losses := [] }

theorem u1607 : Upper (D 10) (R 10) [6,72,160,80,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1607 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1608 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 88 304 417 481 417 417), lower := (rows 7 74 164 88 304 32 64 128 256), losses := [] }

theorem u1608 : Upper (D 10) (R 10) [6,72,160,80,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1608 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1609 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 88 400 289 353 417 289), lower := (rows 7 74 164 88 400 32 64 128 256), losses := [] }

theorem u1609 : Upper (D 10) (R 10) [6,72,160,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1609 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1610 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 104 49 432 464 400 400), lower := (rows 7 74 164 104 49 32 64 128 256), losses := [] }

theorem u1610 : Upper (D 10) (R 10) [6,72,160,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1610 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1611 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 104 273 432 496 432 432), lower := (rows 7 74 164 104 273 32 64 128 256), losses := [] }

theorem u1611 : Upper (D 10) (R 10) [6,72,160,96,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1611 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1612 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 104 304 433 465 401 401), lower := (rows 7 74 164 104 304 32 64 128 256), losses := [] }

theorem u1612 : Upper (D 10) (R 10) [6,72,160,96,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1612 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1613 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 104 400 305 369 433 305), lower := (rows 7 74 164 104 400 32 64 128 256), losses := [] }

theorem u1613 : Upper (D 10) (R 10) [6,72,160,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1613 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1614 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 137 112 304 368 432 304), lower := (rows 7 74 164 137 112 32 64 128 256), losses := [] }

theorem u1614 : Upper (D 10) (R 10) [6,72,160,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1614 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1615 : PairBound 9 := { available := 368, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 137 304 368 368 496 368), lower := (rows 7 74 164 137 304 32 64 128 256), losses := [] }

theorem u1615 : Upper (D 10) (R 10) [6,72,160,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1615 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1616 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 137 336 304 368 432 304), lower := (rows 7 74 164 137 336 32 64 128 256), losses := [] }

theorem u1616 : Upper (D 10) (R 10) [6,72,160,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1616 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1617 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 164 152 49 352 352 480 352), lower := (rows 7 74 164 152 49 32 64 128 256), losses := [] }

theorem u1617 : Upper (D 10) (R 10) [6,72,160,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1617 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1618 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 152 81 288 352 416 288), lower := (rows 7 74 164 152 81 32 64 128 256), losses := [] }

theorem u1618 : Upper (D 10) (R 10) [6,72,160,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1618 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1619 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 164 152 112 289 353 417 289), lower := (rows 7 74 164 152 112 32 64 128 256), losses := [] }

theorem u1619 : Upper (D 10) (R 10) [6,72,160,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1619 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1619
end Delivery.IrregularNine14.P10
