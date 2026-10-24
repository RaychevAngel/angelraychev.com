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

def b1740 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,8),(4,6)], upper := (rows 35 194 13 88 400 288 68 161 289), lower := (rows 35 194 13 88 400 288 68 128 256), losses := [{ target := 8, region := (rows 1 6 4 8 16 32 68 129 0), good := (rows 163 194 207 88 144 32 70 128 0) }] }

theorem u1740 : Upper (D 9) (R 9) [34,192,9,80,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1740 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 106, targets := 1 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 },{ cop := 4, region := 104, targets := 128 }], pairs := [(1,0),(3,0),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 88 400 288 96 133 261), lower := (rows 35 194 13 88 400 288 96 128 256), losses := [] }

theorem u1741 : Upper (D 9) (R 9) [34,192,9,80,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1741 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 2, region := 400, targets := 1 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,0)], upper := (rows 35 194 13 104 148 288 65 400 272), lower := (rows 35 194 13 104 148 288 65 128 256), losses := [] }

theorem u1742 : Upper (D 9) (R 9) [34,192,9,96,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1742 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 104 148 288 80 385 257), lower := (rows 35 194 13 104 148 288 80 128 256), losses := [] }

theorem u1743 : Upper (D 9) (R 9) [34,192,9,96,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1743 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 151, targets := 256 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8),(4,8)], upper := (rows 35 194 13 104 148 288 320 145 273), lower := (rows 35 194 13 104 148 288 320 128 256), losses := [] }

theorem u1744 : Upper (D 9) (R 9) [34,192,9,96,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1744 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 104 273 288 68 144 400), lower := (rows 35 194 13 104 273 288 68 128 256), losses := [] }

theorem u1745 : Upper (D 9) (R 9) [34,192,9,96,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1745 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 35 194 13 104 273 288 80 132 388), lower := (rows 35 194 13 104 273 288 80 128 256), losses := [] }

theorem u1746 : Upper (D 9) (R 9) [34,192,9,96,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1746 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 273 288 192 148 276), lower := (rows 35 194 13 104 273 288 192 128 256), losses := [] }

theorem u1747 : Upper (D 9) (R 9) [34,192,9,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1747 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 384, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 104 276 48 65 384 384), lower := (rows 35 194 13 104 276 48 65 128 256), losses := [] }

theorem u1748 : Upper (D 9) (R 9) [34,192,9,96,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1748 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 276 48 192 385 257), lower := (rows 35 194 13 104 276 48 192 128 256), losses := [] }

theorem u1749 : Upper (D 9) (R 9) [34,192,9,96,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1749 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 2, region := 450, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 35 194 13 104 276 48 320 129 385), lower := (rows 35 194 13 104 276 48 320 128 256), losses := [] }

theorem u1750 : Upper (D 9) (R 9) [34,192,9,96,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1750 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 2, region := 400, targets := 1 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,0)], upper := (rows 35 194 13 104 276 288 65 144 400), lower := (rows 35 194 13 104 276 288 65 128 256), losses := [] }

theorem u1751 : Upper (D 9) (R 9) [34,192,9,96,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1751 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 135, targets := 256 },{ cop := 2, region := 466, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 35 194 13 104 276 288 80 129 385), lower := (rows 35 194 13 104 276 288 80 128 256), losses := [] }

theorem u1752 : Upper (D 9) (R 9) [34,192,9,96,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1752 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 104 276 288 192 145 273), lower := (rows 35 194 13 104 276 288 192 128 256), losses := [] }

theorem u1753 : Upper (D 9) (R 9) [34,192,9,96,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1753 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 2, region := 400, targets := 1 }], pairs := [(2,7),(2,8),(3,7),(3,8),(4,0)], upper := (rows 35 194 13 104 400 288 65 148 276), lower := (rows 35 194 13 104 400 288 65 128 256), losses := [] }

theorem u1754 : Upper (D 9) (R 9) [34,192,9,96,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1754 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 13 104 400 288 68 145 273), lower := (rows 35 194 13 104 400 288 68 128 256), losses := [] }

theorem u1755 : Upper (D 9) (R 9) [34,192,9,96,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1755 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 3, region := 135, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7)], upper := (rows 35 194 13 104 400 288 80 133 261), lower := (rows 35 194 13 104 400 288 80 128 256), losses := [] }

theorem u1756 : Upper (D 9) (R 9) [34,192,9,96,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1756 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 144, camps := [{ cop := 5, region := 211, targets := 256 },{ cop := 6, region := 434, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(4,0),(4,8)], upper := (rows 35 194 13 268 112 288 65 144 400), lower := (rows 35 194 13 268 112 288 65 128 256), losses := [] }

theorem u1757 : Upper (D 9) (R 9) [34,192,9,260,96,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1757 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 301, targets := 64 },{ cop := 5, region := 211, targets := 256 }], pairs := [(0,6),(0,8),(2,6),(3,6)], upper := (rows 35 194 13 268 112 288 80 129 385), lower := (rows 35 194 13 268 112 288 80 128 256), losses := [] }

theorem u1758 : Upper (D 9) (R 9) [34,192,9,260,96,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1758 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 5, region := 211, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 268 112 288 192 145 273), lower := (rows 35 194 13 268 112 288 192 128 256), losses := [] }

theorem u1759 : Upper (D 9) (R 9) [34,192,9,260,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1759 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 80, targets := 416 },{ cop := 4, region := 418, targets := 1 }], pairs := [(1,0),(4,5),(4,7),(4,8)], upper := (rows 35 194 13 280 81 288 68 160 416), lower := (rows 35 194 13 280 81 288 68 128 256), losses := [] }

theorem u1760 : Upper (D 9) (R 9) [34,192,9,272,65,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1760 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 398, targets := 32 },{ cop := 0, region := 80, targets := 384 }], pairs := [(1,5),(2,5),(3,5),(4,7),(4,8)], upper := (rows 35 194 13 280 81 288 96 132 388), lower := (rows 35 194 13 280 81 288 96 128 256), losses := [] }

theorem u1761 : Upper (D 9) (R 9) [34,192,9,272,65,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1761 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 81 288 192 164 292), lower := (rows 35 194 13 280 81 288 192 128 256), losses := [] }

theorem u1762 : Upper (D 9) (R 9) [34,192,9,272,65,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1762 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 394, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 280 112 36 65 384 384), lower := (rows 35 194 13 280 112 36 65 128 256), losses := [] }

theorem u1763 : Upper (D 9) (R 9) [34,192,9,272,96,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1763 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 112 36 192 385 257), lower := (rows 35 194 13 280 112 36 192 128 256), losses := [] }

theorem u1764 : Upper (D 9) (R 9) [34,192,9,272,96,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1764 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1765 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 131, targets := 256 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(4,0)], upper := (rows 35 194 13 280 112 36 320 129 385), lower := (rows 35 194 13 280 112 36 320 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 36 328 128 256), good := (rows 34 194 124 344 112 52 320 128 320) }] }

theorem u1765 : Upper (D 9) (R 9) [34,192,9,272,96,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1765 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1766 : Route 9 := (fun mask => (mask,id))

def c1766 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1766 : Upper (D 9) (R 9) [34,192,9,272,96,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,272,96,256,1] 13 (by decide) (choices 1) [4] r1766 c1766
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u94

def b1767 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 131, targets := 256 },{ cop := 1, region := 289, targets := 64 },{ cop := 2, region := 194, targets := 32 }], pairs := [(0,6),(0,8),(1,5),(1,8)], upper := (rows 35 194 13 280 112 288 68 129 385), lower := (rows 35 194 13 280 112 288 68 128 256), losses := [] }

theorem u1767 : Upper (D 9) (R 9) [34,192,9,272,96,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1767 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 280 112 288 192 133 261), lower := (rows 35 194 13 280 112 288 192 128 256), losses := [] }

theorem u1768 : Upper (D 9) (R 9) [34,192,9,272,96,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1768 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 144, camps := [{ cop := 6, region := 402, targets := 33 }], pairs := [(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 13 296 336 36 65 144 400), lower := (rows 35 194 13 296 336 36 65 128 256), losses := [] }

theorem u1769 : Upper (D 9) (R 9) [34,192,9,288,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1769 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 301, targets := 64 }], pairs := [(0,6),(2,6),(3,6)], upper := (rows 35 194 13 296 336 36 80 129 385), lower := (rows 35 194 13 296 336 36 80 128 256), losses := [] }

theorem u1770 : Upper (D 9) (R 9) [34,192,9,288,320,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1770 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 296 336 36 192 145 273), lower := (rows 35 194 13 296 336 36 192 128 256), losses := [] }

theorem u1771 : Upper (D 9) (R 9) [34,192,9,288,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1771 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 328 145 36 80 416 288), lower := (rows 35 194 13 328 145 36 80 128 256), losses := [] }

theorem u1772 : Upper (D 9) (R 9) [34,192,9,320,129,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1772 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1773 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 364, targets := 128 }], pairs := [(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 328 145 36 96 400 272), lower := (rows 35 194 13 328 145 36 96 128 256), losses := [] }

theorem u1773 : Upper (D 9) (R 9) [34,192,9,320,129,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1773 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 194 13 328 145 36 320 176 304), lower := (rows 35 194 13 328 145 36 320 128 256), losses := [] }

theorem u1774 : Upper (D 9) (R 9) [34,192,9,320,129,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1774 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 364, targets := 128 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 13 328 145 288 68 176 304), lower := (rows 35 194 13 328 145 288 68 128 256), losses := [] }

theorem u1775 : Upper (D 9) (R 9) [34,192,9,320,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1775 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 328 145 288 80 164 292), lower := (rows 35 194 13 328 145 288 80 128 256), losses := [] }

theorem u1776 : Upper (D 9) (R 9) [34,192,9,320,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1776 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 20, camps := [{ cop := 4, region := 364, targets := 128 },{ cop := 2, region := 144, targets := 32 },{ cop := 2, region := 144, targets := 64 },{ cop := 2, region := 144, targets := 256 }], pairs := [(2,7),(3,7),(4,5),(4,6),(4,8)], upper := (rows 35 194 13 328 145 288 96 148 276), lower := (rows 35 194 13 328 145 288 96 128 256), losses := [] }

theorem u1777 : Upper (D 9) (R 9) [34,192,9,320,129,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1777 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 432, targets := 65 }], pairs := [(2,7),(3,7),(4,0),(4,6)], upper := (rows 35 194 13 328 148 48 65 416 288), lower := (rows 35 194 13 328 148 48 65 128 256), losses := [] }

theorem u1778 : Upper (D 9) (R 9) [34,192,9,320,132,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1778 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 4, region := 99, targets := 256 }], pairs := [(0,8),(1,8),(2,7),(3,7)], upper := (rows 35 194 13 328 148 48 96 385 257), lower := (rows 35 194 13 328 148 48 96 128 256), losses := [] }

theorem u1779 : Upper (D 9) (R 9) [34,192,9,320,132,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1779 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1780 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 194 13 328 148 48 320 161 289), lower := (rows 35 194 13 328 148 48 320 128 256), losses := [] }

theorem u1780 : Upper (D 9) (R 9) [34,192,9,320,132,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1780 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1781 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 432, targets := 65 }], pairs := [(1,5),(1,8),(3,7),(4,0),(4,6)], upper := (rows 35 194 13 328 148 288 65 176 304), lower := (rows 35 194 13 328 148 288 65 128 256), losses := [{ target := 5, region := (rows 1 18 4 8 16 0 69 128 256), good := (rows 67 194 77 328 214 256 65 128 256) },{ target := 7, region := (rows 1 2 4 24 16 312 69 0 272), good := (rows 99 66 109 360 380 288 65 0 288) },{ target := 8, region := (rows 1 18 4 8 16 32 69 128 0), good := (rows 99 194 77 72 214 32 65 128 0) }] }

theorem u1781 : Upper (D 9) (R 9) [34,192,9,320,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1781 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1782 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 328 148 288 80 161 289), lower := (rows 35 194 13 328 148 288 80 128 256), losses := [] }

theorem u1782 : Upper (D 9) (R 9) [34,192,9,320,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1782 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 17, camps := [{ cop := 5, region := 72, targets := 129 },{ cop := 2, region := 144, targets := 32 },{ cop := 2, region := 144, targets := 64 },{ cop := 2, region := 144, targets := 256 }], pairs := [(3,0),(3,7),(4,5),(4,6),(4,8)], upper := (rows 35 194 13 328 148 288 96 145 273), lower := (rows 35 194 13 328 148 288 96 128 256), losses := [] }

theorem u1783 : Upper (D 9) (R 9) [34,192,9,320,132,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1783 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6)], upper := (rows 35 194 13 328 176 36 65 400 272), lower := (rows 35 194 13 328 176 36 65 128 256), losses := [] }

theorem u1784 : Upper (D 9) (R 9) [34,192,9,320,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1784 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 13 328 176 36 80 385 257), lower := (rows 35 194 13 328 176 36 80 128 256), losses := [] }

theorem u1785 : Upper (D 9) (R 9) [34,192,9,320,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1785 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(4,8)], upper := (rows 35 194 13 328 176 36 320 145 273), lower := (rows 35 194 13 328 176 36 320 128 256), losses := [] }

theorem u1786 : Upper (D 9) (R 9) [34,192,9,320,160,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1786 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1787 : Route 9 := (fun mask => (mask,id))

def c1787 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1787 : Upper (D 9) (R 9) [34,192,9,320,160,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,160,256,1] 13 (by decide) (choices 1) [4,16] r1787 c1787
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u95
  · exact u96

def b1788 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 144, targets := 256 }], pairs := [(0,6),(1,8),(4,6),(4,8)], upper := (rows 35 194 13 328 176 288 68 145 273), lower := (rows 35 194 13 328 176 288 68 128 256), losses := [{ target := 8, region := (rows 1 70 4 8 17 32 68 133 0), good := (rows 179 194 223 74 176 32 198 128 0) }] }

theorem u1788 : Upper (D 9) (R 9) [34,192,9,320,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1788 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 13 328 176 288 80 133 261), lower := (rows 35 194 13 328 176 288 80 128 256), losses := [] }

theorem u1789 : Upper (D 9) (R 9) [34,192,9,320,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1789 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 194 13 328 273 36 80 160 416), lower := (rows 35 194 13 328 273 36 80 128 256), losses := [] }

theorem u1790 : Upper (D 9) (R 9) [34,192,9,320,257,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1790 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 400, targets := 96 },{ cop := 4, region := 108, targets := 128 }], pairs := [(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 328 273 36 96 144 400), lower := (rows 35 194 13 328 273 36 96 128 256), losses := [] }

theorem u1791 : Upper (D 9) (R 9) [34,192,9,320,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1791 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 273 36 192 176 304), lower := (rows 35 194 13 328 273 36 192 128 256), losses := [] }

theorem u1792 : Upper (D 9) (R 9) [34,192,9,320,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1792 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 76, targets := 32 }], pairs := [(0,6),(2,5),(4,6)], upper := (rows 35 194 13 328 273 48 68 160 416), lower := (rows 35 194 13 328 273 48 68 128 256), losses := [] }

theorem u1793 : Upper (D 9) (R 9) [34,192,9,320,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1793 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 108, targets := 128 },{ cop := 2, region := 400, targets := 32 },{ cop := 2, region := 400, targets := 64 }], pairs := [(2,7),(3,7),(4,5),(4,6)], upper := (rows 35 194 13 328 273 48 96 132 388), lower := (rows 35 194 13 328 273 48 96 128 256), losses := [] }

theorem u1794 : Upper (D 9) (R 9) [34,192,9,320,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1794 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 273 48 192 164 292), lower := (rows 35 194 13 328 273 48 192 128 256), losses := [] }

theorem u1795 : Upper (D 9) (R 9) [34,192,9,320,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1795 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6)], upper := (rows 35 194 13 328 276 48 65 160 416), lower := (rows 35 194 13 328 276 48 65 128 256), losses := [] }

theorem u1796 : Upper (D 9) (R 9) [34,192,9,320,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1796 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 104, targets := 129 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,8),(1,8),(3,0),(3,7)], upper := (rows 35 194 13 328 276 48 96 129 385), lower := (rows 35 194 13 328 276 48 96 128 256), losses := [] }

theorem u1797 : Upper (D 9) (R 9) [34,192,9,320,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1797 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 276 48 192 161 289), lower := (rows 35 194 13 328 276 48 192 128 256), losses := [] }

theorem u1798 : Upper (D 9) (R 9) [34,192,9,320,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1798 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(4,6)], upper := (rows 35 194 13 328 304 33 68 144 400), lower := (rows 35 194 13 328 304 33 68 128 256), losses := [] }

theorem u1799 : Upper (D 9) (R 9) [34,192,9,320,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1799 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P09
