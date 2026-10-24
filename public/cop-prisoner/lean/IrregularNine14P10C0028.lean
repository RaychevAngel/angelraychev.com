import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0010

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1680 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 265 176 304 368 432 304), lower := (rows 7 74 196 265 176 32 64 128 256), losses := [] }

theorem u1680 : Upper (D 10) (R 10) [6,72,192,257,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1680 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 265 304 176 240 176 432), lower := (rows 7 74 196 265 304 32 64 128 256), losses := [] }

theorem u1681 : Upper (D 10) (R 10) [6,72,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1681 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 265 400 48 112 176 304), lower := (rows 7 74 196 265 400 32 64 128 256), losses := [] }

theorem u1682 : Upper (D 10) (R 10) [6,72,192,257,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1682 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 416, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 280 49 416 480 416 416), lower := (rows 7 74 196 280 49 32 64 128 256), losses := [] }

theorem u1683 : Upper (D 10) (R 10) [6,72,192,272,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1683 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 280 145 288 352 416 288), lower := (rows 7 74 196 280 145 32 64 128 256), losses := [] }

theorem u1684 : Upper (D 10) (R 10) [6,72,192,272,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1684 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 280 176 289 353 417 289), lower := (rows 7 74 196 280 176 32 64 128 256), losses := [] }

theorem u1685 : Upper (D 10) (R 10) [6,72,192,272,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1685 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 432, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 49 432 496 432 432), lower := (rows 7 74 196 296 49 32 64 128 256), losses := [] }

theorem u1686 : Upper (D 10) (R 10) [6,72,192,288,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1686 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 145 304 368 432 304), lower := (rows 7 74 196 296 145 32 64 128 256), losses := [] }

theorem u1687 : Upper (D 10) (R 10) [6,72,192,288,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1687 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 305, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 176 305 369 433 305), lower := (rows 7 74 196 296 176 32 64 128 256), losses := [] }

theorem u1688 : Upper (D 10) (R 10) [6,72,192,288,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1688 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 273 176 240 176 432), lower := (rows 7 74 196 296 273 32 64 128 256), losses := [] }

theorem u1689 : Upper (D 10) (R 10) [6,72,192,288,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1689 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 296 400 49 113 177 305), lower := (rows 7 74 196 296 400 32 64 128 256), losses := [] }

theorem u1690 : Upper (D 10) (R 10) [6,72,192,288,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1690 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 392 49 304 368 432 304), lower := (rows 7 74 196 392 49 32 64 128 256), losses := [] }

theorem u1691 : Upper (D 10) (R 10) [6,72,192,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1691 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 392 273 48 112 176 304), lower := (rows 7 74 196 392 273 32 64 128 256), losses := [] }

theorem u1692 : Upper (D 10) (R 10) [6,72,192,384,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1692 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 74 196 392 304 49 113 177 305), lower := (rows 7 74 196 392 304 32 64 128 256), losses := [] }

theorem u1693 : Upper (D 10) (R 10) [6,72,192,384,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1693 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1694 : Route 9 := (fun mask => match mask with | 256 => (128,(fun i => match i.val with | 7 => 8 | 8 => 7 | _ => i)) | _ => (mask,id))

def c1694 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | _ => 0)

theorem u1694 : Upper (D 10) (R 10) [6,72,384,33,96] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,96] 13 (by decide) (choices 1) [16,128] r1694 c1694
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u606
  · exact u607

def r1695 : Route 9 := (fun mask => (mask,id))

def c1695 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1695 : Upper (D 10) (R 10) [6,72,384,33,160] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,160] 13 (by decide) (choices 1) [16,64,256] r1695 c1695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u608
  · exact u609
  · exact u610

def r1696 : Route 9 := (fun mask => (mask,id))

def c1696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1696 : Upper (D 10) (R 10) [6,72,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,72,384,33,192] 13 (by decide) (choices 1) [16,256] r1696 c1696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u611
  · exact u612

def b1697 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 74 388 41 400 112 112 240 368), lower := (rows 7 74 388 41 400 32 64 128 256), losses := [] }

theorem u1697 : Upper (D 10) (R 10) [6,72,384,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1697 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 480, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 74 388 56 49 480 480 480 480), lower := (rows 7 74 388 56 49 32 64 128 256), losses := [] }

theorem u1698 : Upper (D 10) (R 10) [6,72,384,48,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1698 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 56 81 416 480 416 416), lower := (rows 7 74 388 56 81 32 64 128 256), losses := [] }

theorem u1699 : Upper (D 10) (R 10) [6,72,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1699 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 417, camps := [{ cop := 4, region := 10, targets := 384 }], pairs := [(1,7),(1,8)], upper := (rows 7 74 388 56 112 417 481 417 417), lower := (rows 7 74 388 56 112 32 64 128 256), losses := [] }

theorem u1700 : Upper (D 10) (R 10) [6,72,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1700 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 352, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 74 388 56 145 352 352 480 352), lower := (rows 7 74 388 56 145 32 64 128 256), losses := [] }

theorem u1701 : Upper (D 10) (R 10) [6,72,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1701 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 353, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 74 388 56 176 353 353 481 353), lower := (rows 7 74 388 56 176 32 64 128 256), losses := [] }

theorem u1702 : Upper (D 10) (R 10) [6,72,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1702 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 56 208 289 353 417 289), lower := (rows 7 74 388 56 208 32 64 128 256), losses := [] }

theorem u1703 : Upper (D 10) (R 10) [6,72,384,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1703 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 74 388 56 400 97 97 225 353), lower := (rows 7 74 388 56 400 32 64 128 256), losses := [] }

theorem u1704 : Upper (D 10) (R 10) [6,72,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1704 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 73 176 304 368 432 304), lower := (rows 7 74 388 73 176 32 64 128 256), losses := [] }

theorem u1705 : Upper (D 10) (R 10) [6,72,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1705 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 416, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 88 49 416 480 416 416), lower := (rows 7 74 388 88 49 32 64 128 256), losses := [] }

theorem u1706 : Upper (D 10) (R 10) [6,72,384,80,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1706 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 88 176 289 353 417 289), lower := (rows 7 74 388 88 176 32 64 128 256), losses := [] }

theorem u1707 : Upper (D 10) (R 10) [6,72,384,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1707 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 104 49 432 496 432 432), lower := (rows 7 74 388 104 49 32 64 128 256), losses := [] }

theorem u1708 : Upper (D 10) (R 10) [6,72,384,96,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1708 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 104 176 305 369 433 305), lower := (rows 7 74 388 104 176 32 64 128 256), losses := [] }

theorem u1709 : Upper (D 10) (R 10) [6,72,384,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1709 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 137 112 304 368 432 304), lower := (rows 7 74 388 137 112 32 64 128 256), losses := [] }

theorem u1710 : Upper (D 10) (R 10) [6,72,384,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1710 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 137 304 112 112 240 368), lower := (rows 7 74 388 137 304 32 64 128 256), losses := [] }

theorem u1711 : Upper (D 10) (R 10) [6,72,384,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1711 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 137 336 48 112 176 304), lower := (rows 7 74 388 137 336 32 64 128 256), losses := [] }

theorem u1712 : Upper (D 10) (R 10) [6,72,384,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1712 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 352, camps := [{ cop := 0, region := 368, targets := 128 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 74 388 152 49 352 352 480 352), lower := (rows 7 74 388 152 49 32 64 128 256), losses := [] }

theorem u1713 : Upper (D 10) (R 10) [6,72,384,144,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1713 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 152 81 288 352 416 288), lower := (rows 7 74 388 152 81 32 64 128 256), losses := [] }

theorem u1714 : Upper (D 10) (R 10) [6,72,384,144,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1714 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 152 112 289 353 417 289), lower := (rows 7 74 388 152 112 32 64 128 256), losses := [] }

theorem u1715 : Upper (D 10) (R 10) [6,72,384,144,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1715 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 234, targets := 256 }], pairs := [(1,8),(3,8)], upper := (rows 7 74 388 152 273 96 96 224 352), lower := (rows 7 74 388 152 273 32 64 128 256), losses := [] }

theorem u1716 : Upper (D 10) (R 10) [6,72,384,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1716 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1717 : Route 9 := (fun mask => (mask,id))

def c1717 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1717 : Upper (D 10) (R 10) [6,72,384,144,288] 13 := by
  apply FastRouting.sound _ _ [6,72,384,144,288] 13 (by decide) (choices 1) [1,64] r1717 c1717
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u613
  · exact u614

def b1718 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 421, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 152 336 33 97 161 289), lower := (rows 7 74 388 152 336 32 64 128 256), losses := [] }

theorem u1718 : Upper (D 10) (R 10) [6,72,384,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1718 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1719 : Route 9 := (fun mask => (mask,id))

def c1719 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | _ => 0)

theorem u1719 : Upper (D 10) (R 10) [6,72,384,160,33] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160,33] 13 (by decide) (choices 1) [16,64,256] r1719 c1719
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u615
  · exact u616
  · exact u617

def b1720 : PairBound 9 := { available := 304, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 74 388 168 81 304 368 432 304), lower := (rows 7 74 388 168 81 32 64 128 256), losses := [] }

theorem u1720 : Upper (D 10) (R 10) [6,72,384,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1720 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1721 : Route 9 := (fun mask => (mask,id))

def c1721 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1721 : Upper (D 10) (R 10) [6,72,384,160,96] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160,96] 13 (by decide) (choices 1) [1,16,256] r1721 c1721
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u618
  · exact u619
  · exact u620

def b1722 : PairBound 9 := { available := 112, camps := [{ cop := 4, region := 234, targets := 256 }], pairs := [(1,8),(3,8)], upper := (rows 7 74 388 168 273 112 112 240 368), lower := (rows 7 74 388 168 273 32 64 128 256), losses := [] }

theorem u1722 : Upper (D 10) (R 10) [6,72,384,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1722 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1723 : Route 9 := (fun mask => (mask,id))

def c1723 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1723 : Upper (D 10) (R 10) [6,72,384,160,288] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160,288] 13 (by decide) (choices 1) [1,16,64] r1723 c1723
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u621
  · exact u622
  · exact u623

def r1724 : Route 9 := (fun mask => (mask,id))

def c1724 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1724 : Upper (D 10) (R 10) [6,72,384,160,320] 13 := by
  apply FastRouting.sound _ _ [6,72,384,160,320] 13 (by decide) (choices 1) [1,16] r1724 c1724
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u624
  · exact u625

def b1725 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 200 49 304 368 432 304), lower := (rows 7 74 388 200 49 32 64 128 256), losses := [] }

theorem u1725 : Upper (D 10) (R 10) [6,72,384,192,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1725 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 437, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 74 388 200 304 49 113 177 305), lower := (rows 7 74 388 200 304 32 64 128 256), losses := [] }

theorem u1726 : Upper (D 10) (R 10) [6,72,384,192,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1726 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 112, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 74 388 392 49 112 112 240 368), lower := (rows 7 74 388 392 49 32 64 128 256), losses := [] }

theorem u1727 : Upper (D 10) (R 10) [6,72,384,384,33] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1727 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 8, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 74 388 392 112 49 113 177 305), lower := (rows 7 74 388 392 112 32 64 128 256), losses := [] }

theorem u1728 : Upper (D 10) (R 10) [6,72,384,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1728 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 41 152 432 464 400 400), lower := (rows 7 98 100 41 152 32 64 128 256), losses := [] }

theorem u1729 : Upper (D 10) (R 10) [6,96,96,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1729 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 41 400 440 472 408 408), lower := (rows 7 98 100 41 400 32 64 128 256), losses := [] }

theorem u1730 : Upper (D 10) (R 10) [6,96,96,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1730 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 56 145 424 456 392 392), lower := (rows 7 98 100 56 145 32 64 128 256), losses := [] }

theorem u1731 : Upper (D 10) (R 10) [6,96,96,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1731 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 385, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 56 152 417 449 385 385), lower := (rows 7 98 100 56 152 32 64 128 256), losses := [] }

theorem u1732 : Upper (D 10) (R 10) [6,96,96,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1732 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 56 400 425 457 393 393), lower := (rows 7 98 100 56 400 32 64 128 256), losses := [] }

theorem u1733 : Upper (D 10) (R 10) [6,96,96,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1733 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 137 176 312 344 408 280), lower := (rows 7 98 100 137 176 32 64 128 256), losses := [] }

theorem u1734 : Upper (D 10) (R 10) [6,96,96,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1734 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 137 280 432 496 432 432), lower := (rows 7 98 100 137 280 32 64 128 256), losses := [] }

theorem u1735 : Upper (D 10) (R 10) [6,96,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1735 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 137 304 440 472 408 408), lower := (rows 7 98 100 137 304 32 64 128 256), losses := [] }

theorem u1736 : Upper (D 10) (R 10) [6,96,96,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1736 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 137 400 312 376 440 312), lower := (rows 7 98 100 137 400 32 64 128 256), losses := [] }

theorem u1737 : Upper (D 10) (R 10) [6,96,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1737 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 152 280 417 481 417 417), lower := (rows 7 98 100 152 280 32 64 128 256), losses := [] }

theorem u1738 : Upper (D 10) (R 10) [6,96,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1738 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 5, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 7 98 100 152 304 425 457 393 393), lower := (rows 7 98 100 152 304 32 64 128 256), losses := [] }

theorem u1739 : Upper (D 10) (R 10) [6,96,96,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1739 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P10
