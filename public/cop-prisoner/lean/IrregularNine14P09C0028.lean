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

def b1680 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 388 152 336 33 96 137 265), lower := (rows 35 70 388 152 336 33 96 128 256), losses := [] }

theorem u1680 : Upper (D 9) (R 9) [34,68,384,144,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1680 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1681 : Route 9 := (fun mask => (mask,id))

def c1681 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1681 : Upper (D 9) (R 9) [34,68,384,144,320,8,1] 13 := by
  apply FastRouting.sound _ _ [34,68,384,144,320,8,1] 13 (by decide) (choices 1) [1,32] r1681 c1681
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u90
  · exact u91

def b1682 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 122, targets := 1 },{ cop := 0, region := 388, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(4,0)], upper := (rows 35 70 388 152 336 40 96 129 257), lower := (rows 35 70 388 152 336 40 96 128 256), losses := [] }

theorem u1682 : Upper (D 9) (R 9) [34,68,384,144,320,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1682 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1683 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 2, region := 99, targets := 256 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 35 70 388 168 336 33 65 152 280), lower := (rows 35 70 388 168 336 33 65 128 256), losses := [] }

theorem u1683 : Upper (D 9) (R 9) [34,68,384,160,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1683 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1684 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 107, targets := 256 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(1,8),(3,8)], upper := (rows 35 70 388 168 336 33 72 145 273), lower := (rows 35 70 388 168 336 33 72 128 256), losses := [] }

theorem u1684 : Upper (D 9) (R 9) [34,68,384,160,320,1,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1684 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1685 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 82, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 70 388 168 336 33 80 137 265), lower := (rows 35 70 388 168 336 33 80 128 256), losses := [] }

theorem u1685 : Upper (D 9) (R 9) [34,68,384,160,320,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1685 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1686 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 115, targets := 128 },{ cop := 0, region := 396, targets := 64 }], pairs := [(0,7),(1,7),(2,6),(4,7)], upper := (rows 35 70 388 168 336 48 65 137 265), lower := (rows 35 70 388 168 336 48 65 128 256), losses := [] }

theorem u1686 : Upper (D 9) (R 9) [34,68,384,160,320,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1686 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1687 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 122, targets := 1 }], pairs := [(1,0),(3,0),(4,0)], upper := (rows 35 70 388 168 336 48 72 129 257), lower := (rows 35 70 388 168 336 48 72 128 256), losses := [] }

theorem u1687 : Upper (D 9) (R 9) [34,68,384,160,320,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1687 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1688 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 92, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,7)], upper := (rows 35 194 13 28 112 288 65 384 384), lower := (rows 35 194 13 28 112 288 65 128 256), losses := [] }

theorem u1688 : Upper (D 9) (R 9) [34,192,9,20,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1688 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1689 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 112 288 192 385 257), lower := (rows 35 194 13 28 112 288 192 128 256), losses := [] }

theorem u1689 : Upper (D 9) (R 9) [34,192,9,20,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1689 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1690 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 143, targets := 256 },{ cop := 5, region := 80, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 28 112 288 320 129 385), lower := (rows 35 194 13 28 112 288 320 128 256), losses := [] }

theorem u1690 : Upper (D 9) (R 9) [34,192,9,20,96,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1690 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1691 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 195, targets := 256 },{ cop := 6, region := 434, targets := 1 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,0),(1,8),(4,0)], upper := (rows 35 194 13 28 336 288 65 160 416), lower := (rows 35 194 13 28 336 288 65 128 256), losses := [] }

theorem u1691 : Upper (D 9) (R 9) [34,192,9,20,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1691 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1692 : PairBound 9 := { available := 129, camps := [{ cop := 5, region := 80, targets := 129 },{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,0),(4,7)], upper := (rows 35 194 13 28 336 288 96 129 385), lower := (rows 35 194 13 28 336 288 96 128 256), losses := [] }

theorem u1692 : Upper (D 9) (R 9) [34,192,9,20,320,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1692 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1693 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 28 336 288 192 161 289), lower := (rows 35 194 13 28 336 288 192 128 256), losses := [] }

theorem u1693 : Upper (D 9) (R 9) [34,192,9,20,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1693 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1694 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 92, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,7)], upper := (rows 35 194 13 56 84 288 65 384 384), lower := (rows 35 194 13 56 84 288 65 128 256), losses := [] }

theorem u1694 : Upper (D 9) (R 9) [34,192,9,48,68,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1694 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1695 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 84 288 192 385 257), lower := (rows 35 194 13 56 84 288 192 128 256), losses := [] }

theorem u1695 : Upper (D 9) (R 9) [34,192,9,48,68,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1695 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1696 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 466, targets := 32 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(3,6),(4,5)], upper := (rows 35 194 13 56 84 288 320 129 385), lower := (rows 35 194 13 56 84 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 226 12 120 124 352 352 128 352) },{ target := 6, region := (rows 3 2 4 24 16 375 0 135 263), good := (rows 419 419 429 56 444 288 288 128 288) }] }

theorem u1696 : Upper (D 9) (R 9) [34,192,9,48,68,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1696 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1697 : PairBound 9 := { available := 384, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 56 336 36 65 384 384), lower := (rows 35 194 13 56 336 36 65 128 256), losses := [] }

theorem u1697 : Upper (D 9) (R 9) [34,192,9,48,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1697 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1698 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 56 336 36 192 385 257), lower := (rows 35 194 13 56 336 36 192 128 256), losses := [] }

theorem u1698 : Upper (D 9) (R 9) [34,192,9,48,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1698 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1699 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 56 336 36 320 129 385), lower := (rows 35 194 13 56 336 36 320 128 256), losses := [] }

theorem u1699 : Upper (D 9) (R 9) [34,192,9,48,320,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1699 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1700 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 76, targets := 416 }], pairs := [(2,5),(2,7),(2,8),(3,5),(3,7)], upper := (rows 35 194 13 76 176 288 65 400 272), lower := (rows 35 194 13 76 176 288 65 128 256), losses := [] }

theorem u1700 : Upper (D 9) (R 9) [34,192,9,68,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1700 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1701 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 76 176 288 80 385 257), lower := (rows 35 194 13 76 176 288 80 128 256), losses := [] }

theorem u1701 : Upper (D 9) (R 9) [34,192,9,68,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1701 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1702 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(1,0),(4,0),(4,6),(4,8)], upper := (rows 35 194 13 76 176 288 320 145 273), lower := (rows 35 194 13 76 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 18 352 352 128 256), good := (rows 114 242 12 108 242 352 352 128 352) }] }

theorem u1702 : Upper (D 9) (R 9) [34,192,9,68,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1702 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1703 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 194 13 76 273 288 80 160 416), lower := (rows 35 194 13 76 273 288 80 128 256), losses := [] }

theorem u1703 : Upper (D 9) (R 9) [34,192,9,68,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1703 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1704 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 76 273 288 96 144 400), lower := (rows 35 194 13 76 273 288 96 128 256), losses := [] }

theorem u1704 : Upper (D 9) (R 9) [34,192,9,68,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1704 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1705 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 76 273 288 192 176 304), lower := (rows 35 194 13 76 273 288 192 128 256), losses := [] }

theorem u1705 : Upper (D 9) (R 9) [34,192,9,68,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1705 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1706 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 76, targets := 416 }], pairs := [(2,5),(2,7),(2,8),(3,5),(3,7)], upper := (rows 35 194 13 76 400 288 65 176 304), lower := (rows 35 194 13 76 400 288 65 128 256), losses := [] }

theorem u1706 : Upper (D 9) (R 9) [34,192,9,68,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1706 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1707 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 13 76 400 288 80 161 289), lower := (rows 35 194 13 76 400 288 80 128 256), losses := [] }

theorem u1707 : Upper (D 9) (R 9) [34,192,9,68,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1707 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1708 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 76 400 288 96 145 273), lower := (rows 35 194 13 76 400 288 96 128 256), losses := [] }

theorem u1708 : Upper (D 9) (R 9) [34,192,9,68,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1708 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1709 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 92, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,7)], upper := (rows 35 194 13 88 52 288 65 384 384), lower := (rows 35 194 13 88 52 288 65 128 256), losses := [] }

theorem u1709 : Upper (D 9) (R 9) [34,192,9,80,36,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1709 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1710 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 52 288 192 385 257), lower := (rows 35 194 13 88 52 288 192 128 256), losses := [] }

theorem u1710 : Upper (D 9) (R 9) [34,192,9,80,36,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1710 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1711 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(1,5),(3,0),(3,5),(4,6)], upper := (rows 35 194 13 88 52 288 320 129 385), lower := (rows 35 194 13 88 52 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 24 16 352 352 128 256), good := (rows 98 226 12 120 124 352 352 128 352) },{ target := 5, region := (rows 1 23 4 24 16 0 373 133 261), good := (rows 451 194 463 90 478 320 320 128 320) }] }

theorem u1711 : Upper (D 9) (R 9) [34,192,9,80,36,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1711 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1712 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 78, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 194 13 88 145 288 68 416 288), lower := (rows 35 194 13 88 145 288 68 128 256), losses := [] }

theorem u1712 : Upper (D 9) (R 9) [34,192,9,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1712 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1713 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 364, targets := 128 },{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(1,0),(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 88 145 288 96 388 260), lower := (rows 35 194 13 88 145 288 96 128 256), losses := [] }

theorem u1713 : Upper (D 9) (R 9) [34,192,9,80,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1713 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1714 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 364, targets := 128 },{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(1,0),(2,7),(3,7),(4,6)], upper := (rows 35 194 13 88 145 288 320 164 292), lower := (rows 35 194 13 88 145 288 320 128 256), losses := [{ target := 6, region := (rows 3 2 4 8 22 356 0 132 260), good := (rows 51 179 445 56 145 288 288 128 288) }] }

theorem u1714 : Upper (D 9) (R 9) [34,192,9,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1714 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1715 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 },{ cop := 3, region := 418, targets := 1 }], pairs := [(0,6),(0,7),(1,0),(4,0),(4,6)], upper := (rows 35 194 13 88 148 288 65 416 288), lower := (rows 35 194 13 88 148 288 65 128 256), losses := [] }

theorem u1715 : Upper (D 9) (R 9) [34,192,9,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1715 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1716 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 88 148 288 96 385 257), lower := (rows 35 194 13 88 148 288 96 128 256), losses := [{ target := 7, region := (rows 3 2 4 24 16 311 383 0 263), good := (rows 355 355 365 120 380 352 96 0 352) }] }

theorem u1716 : Upper (D 9) (R 9) [34,192,9,80,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1716 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1717 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 },{ cop := 2, region := 432, targets := 64 }], pairs := [(0,6),(0,7),(3,7),(4,6),(4,8)], upper := (rows 35 194 13 88 148 288 320 161 289), lower := (rows 35 194 13 88 148 288 320 128 256), losses := [{ target := 7, region := (rows 3 2 4 24 16 375 375 0 263), good := (rows 355 355 365 120 380 352 352 0 352) },{ target := 8, region := (rows 1 2 4 8 20 32 64 129 0), good := (rows 163 194 157 88 148 32 64 128 0) }] }

theorem u1717 : Upper (D 9) (R 9) [34,192,9,80,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1717 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1718 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 2, region := 432, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 88 176 288 65 388 260), lower := (rows 35 194 13 88 176 288 65 128 256), losses := [] }

theorem u1718 : Upper (D 9) (R 9) [34,192,9,80,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1718 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1719 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 88 176 288 68 385 257), lower := (rows 35 194 13 88 176 288 68 128 256), losses := [] }

theorem u1719 : Upper (D 9) (R 9) [34,192,9,80,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1719 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1720 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 450, targets := 32 },{ cop := 2, region := 432, targets := 64 }], pairs := [(1,0),(1,5),(3,0),(4,0),(4,6)], upper := (rows 35 194 13 88 176 288 320 133 261), lower := (rows 35 194 13 88 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 18 4 27 18 352 352 128 256), good := (rows 122 250 12 122 250 352 352 128 352) }] }

theorem u1720 : Upper (D 9) (R 9) [34,192,9,80,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1720 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1721 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 108, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 88 273 36 96 384 384), lower := (rows 35 194 13 88 273 36 96 128 256), losses := [] }

theorem u1721 : Upper (D 9) (R 9) [34,192,9,80,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1721 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1722 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 273 36 192 416 288), lower := (rows 35 194 13 88 273 36 192 128 256), losses := [] }

theorem u1722 : Upper (D 9) (R 9) [34,192,9,80,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1722 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1723 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 76, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(2,8)], upper := (rows 35 194 13 88 273 36 320 160 416), lower := (rows 35 194 13 88 273 36 320 128 256), losses := [] }

theorem u1723 : Upper (D 9) (R 9) [34,192,9,80,257,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1723 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1724 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 194 13 88 273 288 68 160 416), lower := (rows 35 194 13 88 273 288 68 128 256), losses := [] }

theorem u1724 : Upper (D 9) (R 9) [34,192,9,80,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1724 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1725 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 108, targets := 128 },{ cop := 2, region := 482, targets := 1 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(1,0),(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 88 273 288 96 132 388), lower := (rows 35 194 13 88 273 288 96 128 256), losses := [] }

theorem u1725 : Upper (D 9) (R 9) [34,192,9,80,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1725 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1726 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 273 288 192 164 292), lower := (rows 35 194 13 88 273 288 192 128 256), losses := [] }

theorem u1726 : Upper (D 9) (R 9) [34,192,9,80,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1726 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1727 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(4,0),(4,6)], upper := (rows 35 194 13 88 276 288 65 160 416), lower := (rows 35 194 13 88 276 288 65 128 256), losses := [] }

theorem u1727 : Upper (D 9) (R 9) [34,192,9,80,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1727 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1728 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 104, targets := 129 },{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(3,0),(3,7)], upper := (rows 35 194 13 88 276 288 96 129 385), lower := (rows 35 194 13 88 276 288 96 128 256), losses := [] }

theorem u1728 : Upper (D 9) (R 9) [34,192,9,80,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1728 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1729 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 276 288 192 161 289), lower := (rows 35 194 13 88 276 288 192 128 256), losses := [] }

theorem u1729 : Upper (D 9) (R 9) [34,192,9,80,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1729 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1730 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 3, region := 386, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,6)], upper := (rows 35 194 13 88 304 36 65 384 384), lower := (rows 35 194 13 88 304 36 65 128 256), losses := [] }

theorem u1730 : Upper (D 9) (R 9) [34,192,9,80,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1730 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1731 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 88 304 36 192 385 257), lower := (rows 35 194 13 88 304 36 192 128 256), losses := [] }

theorem u1731 : Upper (D 9) (R 9) [34,192,9,80,288,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1731 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1732 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 13 88 304 36 320 129 385), lower := (rows 35 194 13 88 304 36 320 128 256), losses := [] }

theorem u1732 : Upper (D 9) (R 9) [34,192,9,80,288,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1732 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1733 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 88 400 33 68 416 288), lower := (rows 35 194 13 88 400 33 68 128 256), losses := [] }

theorem u1733 : Upper (D 9) (R 9) [34,192,9,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1733 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1734 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 2, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 13 88 400 33 96 388 260), lower := (rows 35 194 13 88 400 33 96 128 256), losses := [] }

theorem u1734 : Upper (D 9) (R 9) [34,192,9,80,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1734 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1735 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 74, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 88 400 33 320 164 292), lower := (rows 35 194 13 88 400 33 320 128 256), losses := [] }

theorem u1735 : Upper (D 9) (R 9) [34,192,9,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1735 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1736 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 88 400 36 65 416 288), lower := (rows 35 194 13 88 400 36 65 128 256), losses := [] }

theorem u1736 : Upper (D 9) (R 9) [34,192,9,80,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1736 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1737 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 13 88 400 36 96 385 257), lower := (rows 35 194 13 88 400 36 96 128 256), losses := [] }

theorem u1737 : Upper (D 9) (R 9) [34,192,9,80,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1737 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1738 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 88 400 36 320 161 289), lower := (rows 35 194 13 88 400 36 320 128 256), losses := [] }

theorem u1738 : Upper (D 9) (R 9) [34,192,9,80,384,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1738 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1739 : Route 9 := (fun mask => (mask,id))

def c1739 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1739 : Upper (D 9) (R 9) [34,192,9,80,384,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,80,384,256,1] 13 (by decide) (choices 1) [4,32] r1739 c1739
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u92
  · exact u93

#print axioms u1739
end Delivery.IrregularNine14.P09
