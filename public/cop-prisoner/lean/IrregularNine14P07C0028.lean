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

def b1680 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 73 274 160 65 160 416), lower := (rows 7 42 84 73 274 160 65 128 256), losses := [] }

theorem u1680 : Upper (D 7) (R 7) [6,40,80,65,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1680 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1681 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(1,6),(3,1),(4,5),(4,6)], upper := (rows 7 42 84 73 274 160 96 129 385), lower := (rows 7 42 84 73 274 160 96 128 256), losses := [] }

theorem u1681 : Upper (D 7) (R 7) [6,40,80,65,258,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1681 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1682 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 232, targets := 2 }], pairs := [(1,0),(1,6),(3,1),(4,6)], upper := (rows 7 42 84 73 274 160 192 161 289), lower := (rows 7 42 84 73 274 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 4 8 16 224 224 128 256), good := (rows 6 106 116 106 274 224 224 224 256) }] }

theorem u1682 : Upper (D 7) (R 7) [6,40,80,65,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1682 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 73 304 160 65 130 386), lower := (rows 7 42 84 73 304 160 65 128 256), losses := [] }

theorem u1683 : Upper (D 7) (R 7) [6,40,80,65,288,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1683 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 79, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 84 73 304 160 66 129 385), lower := (rows 7 42 84 73 304 160 66 128 256), losses := [] }

theorem u1684 : Upper (D 7) (R 7) [6,40,80,65,288,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1684 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 200, targets := 32 }], pairs := [(1,0),(1,6),(3,5),(4,6)], upper := (rows 7 42 84 73 304 160 192 131 259), lower := (rows 7 42 84 73 304 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 224 224 128 256), good := (rows 6 106 116 106 372 224 224 224 256) }] }

theorem u1685 : Upper (D 7) (R 7) [6,40,80,65,288,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1685 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 72, targets := 162 },{ cop := 3, region := 162, targets := 1 }], pairs := [(1,0),(3,1),(3,5),(3,7)], upper := (rows 7 42 84 73 400 160 65 162 290), lower := (rows 7 42 84 73 400 160 65 128 256), losses := [] }

theorem u1686 : Upper (D 7) (R 7) [6,40,80,65,384,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1686 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 160 }], pairs := [(3,5),(3,7),(4,1),(4,6)], upper := (rows 7 42 84 73 400 160 66 161 289), lower := (rows 7 42 84 73 400 160 66 128 256), losses := [] }

theorem u1687 : Upper (D 7) (R 7) [6,40,80,65,384,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1687 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 4, region := 100, targets := 3 }], pairs := [(1,6),(2,0),(2,1),(4,6)], upper := (rows 7 42 84 73 400 160 96 131 259), lower := (rows 7 42 84 73 400 160 96 128 256), losses := [] }

theorem u1688 : Upper (D 7) (R 7) [6,40,80,65,384,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1688 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 0, region := 72, targets := 160 }], pairs := [(2,1),(3,5),(3,7),(4,1)], upper := (rows 7 42 84 74 273 160 65 160 416), lower := (rows 7 42 84 74 273 160 65 128 256), losses := [] }

theorem u1689 : Upper (D 7) (R 7) [6,40,80,66,257,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1689 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 74, targets := 129 }], pairs := [(1,0),(1,7),(3,0),(3,7)], upper := (rows 7 42 84 74 273 160 96 129 385), lower := (rows 7 42 84 74 273 160 96 128 256), losses := [] }

theorem u1690 : Upper (D 7) (R 7) [6,40,80,66,257,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1690 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 74, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 74 273 160 192 161 289), lower := (rows 7 42 84 74 273 160 192 128 256), losses := [] }

theorem u1691 : Upper (D 7) (R 7) [6,40,80,66,257,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1691 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 3, region := 116, targets := 2 }], pairs := [(2,1),(4,0),(4,1),(4,6)], upper := (rows 7 42 84 137 176 96 65 386 258), lower := (rows 7 42 84 137 176 96 65 128 256), losses := [] }

theorem u1692 : Upper (D 7) (R 7) [6,40,80,129,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1692 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 118, targets := 1 },{ cop := 0, region := 392, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 42 84 137 176 96 66 385 257), lower := (rows 7 42 84 137 176 96 66 128 256), losses := [] }

theorem u1693 : Upper (D 7) (R 7) [6,40,80,129,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1693 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 },{ cop := 3, region := 354, targets := 128 }], pairs := [(1,7),(3,5),(3,6)], upper := (rows 7 42 84 137 176 96 320 131 259), lower := (rows 7 42 84 137 176 96 320 128 256), losses := [] }

theorem u1694 : Upper (D 7) (R 7) [6,40,80,129,160,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1694 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1695 : Route 9 := (fun mask => (mask,id))

def c1695 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1695 : Upper (D 7) (R 7) [6,40,80,129,160,256,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,256,1] 13 (by decide) (choices 1) [2,64] r1695 c1695
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u62
  · exact u63

def r1696 : Route 9 := (fun mask => (mask,id))

def c1696 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1696 : Upper (D 7) (R 7) [6,40,80,129,160,256,2] 13 := by
  apply FastRouting.sound _ _ [6,40,80,129,160,256,2] 13 (by decide) (choices 1) [1,64] r1696 c1696
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u64
  · exact u65

def b1697 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 84 137 274 96 65 160 416), lower := (rows 7 42 84 137 274 96 65 128 256), losses := [] }

theorem u1697 : Upper (D 7) (R 7) [6,40,80,129,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1697 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 137 274 96 96 129 385), lower := (rows 7 42 84 137 274 96 96 128 256), losses := [] }

theorem u1698 : Upper (D 7) (R 7) [6,40,80,129,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1698 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 232, targets := 2 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(2,1),(3,1),(4,7)], upper := (rows 7 42 84 137 274 96 192 161 289), lower := (rows 7 42 84 137 274 96 192 128 256), losses := [{ target := 1, region := (rows 1 0 20 9 16 255 203 137 265), good := (rows 493 488 116 489 372 96 224 224 256) },{ target := 7, region := (rows 1 2 4 8 17 100 64 0 257), good := (rows 311 42 116 281 274 96 96 0 256) }] }

theorem u1699 : Upper (D 7) (R 7) [6,40,80,129,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1699 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 }], pairs := [(3,5),(3,6),(4,0),(4,6)], upper := (rows 7 42 84 137 304 96 65 130 386), lower := (rows 7 42 84 137 304 96 65 128 256), losses := [] }

theorem u1700 : Upper (D 7) (R 7) [6,40,80,129,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1700 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 66 },{ cop := 3, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 7 42 84 137 304 96 66 129 385), lower := (rows 7 42 84 137 304 96 66 128 256), losses := [] }

theorem u1701 : Upper (D 7) (R 7) [6,40,80,129,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1701 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 136, targets := 32 },{ cop := 0, region := 136, targets := 64 },{ cop := 3, region := 98, targets := 1 }], pairs := [(1,0),(3,5),(3,6),(4,7)], upper := (rows 7 42 84 137 304 96 192 131 259), lower := (rows 7 42 84 137 304 96 192 128 256), losses := [{ target := 7, region := (rows 1 2 4 8 17 100 64 0 257), good := (rows 311 42 116 281 304 96 96 0 256) }] }

theorem u1702 : Upper (D 7) (R 7) [6,40,80,129,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1702 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 84 137 400 34 65 224 352), lower := (rows 7 42 84 137 400 34 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 84 43 64 192 320), good := (rows 54 42 468 170 400 34 500 128 256) }] }

theorem u1703 : Upper (D 7) (R 7) [6,40,80,129,384,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1703 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 34, targets := 1 },{ cop := 3, region := 34, targets := 64 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 84 137 400 34 96 193 321), lower := (rows 7 42 84 137 400 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 7 9 25 32 98 129 257), good := (rows 477 124 84 413 400 100 96 128 256) }] }

theorem u1704 : Upper (D 7) (R 7) [6,40,80,129,384,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1704 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,7),(2,0),(4,0),(4,6)], upper := (rows 7 42 84 137 400 96 65 162 290), lower := (rows 7 42 84 137 400 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 100 8 91 100 64 131 259), good := (rows 438 446 116 408 400 116 500 128 256) }] }

theorem u1705 : Upper (D 7) (R 7) [6,40,80,129,384,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1705 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 1 },{ cop := 3, region := 98, targets := 128 }], pairs := [(1,0),(1,7),(3,1),(4,1)], upper := (rows 7 42 84 137 400 96 66 161 289), lower := (rows 7 42 84 137 400 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 9 25 100 64 129 257), good := (rows 445 56 116 409 400 96 96 128 256) }] }

theorem u1706 : Upper (D 7) (R 7) [6,40,80,129,384,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1706 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 137 400 96 96 131 259), lower := (rows 7 42 84 137 400 96 96 128 256), losses := [] }

theorem u1707 : Upper (D 7) (R 7) [6,40,80,129,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1707 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 288, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 145 96 65 416 288), lower := (rows 7 42 84 138 145 96 65 128 256), losses := [] }

theorem u1708 : Upper (D 7) (R 7) [6,40,80,130,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1708 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 138 145 96 96 385 257), lower := (rows 7 42 84 138 145 96 96 128 256), losses := [] }

theorem u1709 : Upper (D 7) (R 7) [6,40,80,130,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1709 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 356, targets := 128 }], pairs := [(2,1),(2,7),(4,1)], upper := (rows 7 42 84 138 145 96 320 161 289), lower := (rows 7 42 84 138 145 96 320 128 256), losses := [] }

theorem u1710 : Upper (D 7) (R 7) [6,40,80,130,129,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1710 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 138, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 138 273 96 65 160 416), lower := (rows 7 42 84 138 273 96 65 128 256), losses := [] }

theorem u1711 : Upper (D 7) (R 7) [6,40,80,130,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1711 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 138 273 96 96 129 385), lower := (rows 7 42 84 138 273 96 96 128 256), losses := [] }

theorem u1712 : Upper (D 7) (R 7) [6,40,80,130,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1712 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 6, region := 42, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 138 273 96 192 161 289), lower := (rows 7 42 84 138 273 96 192 128 256), losses := [] }

theorem u1713 : Upper (D 7) (R 7) [6,40,80,130,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1713 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1714 : Route 9 := (fun mask => (mask,id))

def c1714 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1714 : Upper (D 7) (R 7) [6,40,80,130,384,1,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384,1,1] 13 (by decide) (choices 1) [32,64] r1714 c1714
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u66
  · exact u67

def r1715 : Route 9 := (fun mask => (mask,id))

def c1715 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1715 : Upper (D 7) (R 7) [6,40,80,130,384,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384,1,32] 13 (by decide) (choices 1) [1,64] r1715 c1715
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u68
  · exact u69

def r1716 : Route 9 := (fun mask => (mask,id))

def c1716 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1716 : Upper (D 7) (R 7) [6,40,80,130,384,64,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,130,384,64,1] 13 (by decide) (choices 1) [1,32] r1716 c1716
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u70
  · exact u71

def b1717 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 138 400 96 96 129 257), lower := (rows 7 42 84 138 400 96 96 128 256), losses := [] }

theorem u1717 : Upper (D 7) (R 7) [6,40,80,130,384,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1717 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 76, targets := 34 }], pairs := [(2,1),(2,5),(3,1)], upper := (rows 7 42 84 200 145 288 65 162 290), lower := (rows 7 42 84 200 145 288 65 128 256), losses := [] }

theorem u1718 : Upper (D 7) (R 7) [6,40,80,192,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1718 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 66 }], pairs := [(2,0),(4,1),(4,6)], upper := (rows 7 42 84 200 145 288 66 161 289), lower := (rows 7 42 84 200 145 288 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 288 67 128 256), good := (rows 70 106 92 200 220 288 66 128 288) }] }

theorem u1719 : Upper (D 7) (R 7) [6,40,80,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1719 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,7),(4,5),(4,6)], upper := (rows 7 42 84 200 145 288 96 131 259), lower := (rows 7 42 84 200 145 288 96 128 256), losses := [{ target := 7, region := (rows 1 2 20 8 16 305 375 0 257), good := (rows 359 106 116 72 373 352 96 0 352) }] }

theorem u1720 : Upper (D 7) (R 7) [6,40,80,192,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1720 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 258, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,6)], upper := (rows 7 42 84 200 176 33 65 386 258), lower := (rows 7 42 84 200 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 50 32 64 131 259), good := (rows 406 442 92 200 176 432 456 128 256) }] }

theorem u1721 : Upper (D 7) (R 7) [6,40,80,192,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1721 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 78, targets := 1 },{ cop := 0, region := 432, targets := 2 }], pairs := [(1,0),(2,0),(3,0),(4,1)], upper := (rows 7 42 84 200 176 33 66 385 257), lower := (rows 7 42 84 200 176 33 66 128 256), losses := [] }

theorem u1722 : Upper (D 7) (R 7) [6,40,80,192,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1722 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(2,5),(3,5),(4,6)], upper := (rows 7 42 84 200 176 33 320 131 259), lower := (rows 7 42 84 200 176 33 320 128 256), losses := [{ target := 5, region := (rows 1 2 20 57 16 0 353 129 257), good := (rows 463 74 92 200 220 457 320 128 320) }] }

theorem u1723 : Upper (D 7) (R 7) [6,40,80,192,160,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1723 [(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 200, targets := 32 },{ cop := 0, region := 432, targets := 64 }], pairs := [(1,6),(3,5),(4,6)], upper := (rows 7 42 84 200 176 288 65 131 259), lower := (rows 7 42 84 200 176 288 65 128 256), losses := [{ target := 6, region := (rows 1 10 4 8 89 353 0 129 257), good := (rows 439 58 52 186 176 288 433 128 288) }] }

theorem u1724 : Upper (D 7) (R 7) [6,40,80,192,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1724 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 78, targets := 1 }], pairs := [(1,0),(2,0),(3,0)], upper := (rows 7 42 84 200 176 288 66 129 257), lower := (rows 7 42 84 200 176 288 66 128 256), losses := [] }

theorem u1725 : Upper (D 7) (R 7) [6,40,80,192,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1725 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 7 42 84 200 273 33 66 160 416), lower := (rows 7 42 84 200 273 33 66 128 256), losses := [] }

theorem u1726 : Upper (D 7) (R 7) [6,40,80,192,257,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1726 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 100, targets := 130 },{ cop := 5, region := 202, targets := 1 }], pairs := [(1,0),(2,1),(2,7),(3,0)], upper := (rows 7 42 84 200 273 33 96 130 386), lower := (rows 7 42 84 200 273 33 96 128 256), losses := [] }

theorem u1727 : Upper (D 7) (R 7) [6,40,80,192,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1727 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 200 273 33 192 162 290), lower := (rows 7 42 84 200 273 33 192 128 256), losses := [] }

theorem u1728 : Upper (D 7) (R 7) [6,40,80,192,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1728 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 84 200 274 33 65 160 416), lower := (rows 7 42 84 200 274 33 65 128 256), losses := [] }

theorem u1729 : Upper (D 7) (R 7) [6,40,80,192,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1729 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 232, targets := 2 },{ cop := 0, region := 400, targets := 32 }], pairs := [(0,7),(2,7),(3,1),(4,5)], upper := (rows 7 42 84 200 274 33 96 129 385), lower := (rows 7 42 84 200 274 33 96 128 256), losses := [] }

theorem u1730 : Upper (D 7) (R 7) [6,40,80,192,258,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1730 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 200 274 33 192 161 289), lower := (rows 7 42 84 200 274 33 192 128 256), losses := [] }

theorem u1731 : Upper (D 7) (R 7) [6,40,80,192,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1731 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,6)], upper := (rows 7 42 84 200 304 33 65 130 386), lower := (rows 7 42 84 200 304 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 50 32 64 131 259), good := (rows 406 442 92 200 304 432 456 128 256) }] }

theorem u1732 : Upper (D 7) (R 7) [6,40,80,192,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1732 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 200, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 200 304 33 66 129 385), lower := (rows 7 42 84 200 304 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 8 51 33 64 161 289), good := (rows 437 440 84 204 432 433 84 128 256) }] }

theorem u1733 : Upper (D 7) (R 7) [6,40,80,192,288,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1733 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 7 42 84 200 304 33 192 131 259), lower := (rows 7 42 84 200 304 33 192 128 256), losses := [] }

theorem u1734 : Upper (D 7) (R 7) [6,40,80,192,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1734 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 400, targets := 65 }], pairs := [(1,6),(2,0),(4,0),(4,6)], upper := (rows 7 42 84 200 400 33 65 162 290), lower := (rows 7 42 84 200 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 68 8 19 32 64 130 258), good := (rows 406 442 84 204 400 48 84 128 256) },{ target := 6, region := (rows 1 10 4 8 123 97 0 139 267), good := (rows 439 442 52 442 400 433 433 128 256) }] }

theorem u1735 : Upper (D 7) (R 7) [6,40,80,192,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1735 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1736 : Route 9 := (fun mask => (mask,id))

def c1736 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1736 : Upper (D 7) (R 7) [6,40,80,192,384,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,1,2] 13 (by decide) (choices 1) [1,32] r1736 c1736
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u72
  · exact u73

def r1737 : Route 9 := (fun mask => (mask,id))

def c1737 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1737 : Upper (D 7) (R 7) [6,40,80,192,384,1,32] 13 := by
  apply FastRouting.sound _ _ [6,40,80,192,384,1,32] 13 (by decide) (choices 1) [1,2] r1737 c1737
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u74
  · exact u75

def b1738 : PairBound 9 := { available := 96, camps := [{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(3,1),(4,1)], upper := (rows 7 42 84 265 145 160 66 224 352), lower := (rows 7 42 84 265 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 255 75 223 351), good := (rows 486 490 500 490 500 160 482 160 256) },{ target := 1, region := (rows 1 0 4 9 17 245 64 196 324), good := (rows 445 40 500 313 185 160 480 160 256) }] }

theorem u1738 : Upper (D 7) (R 7) [6,40,80,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1738 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1739 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 3, region := 226, targets := 1 }], pairs := [(1,0),(2,0),(2,1),(3,7)], upper := (rows 7 42 84 265 145 160 96 194 322), lower := (rows 7 42 84 265 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 25 16 32 98 0 259), good := (rows 335 362 92 265 281 96 96 0 256) }] }

theorem u1739 : Upper (D 7) (R 7) [6,40,80,257,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1739 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1739
end Delivery.IrregularNine14.P07
