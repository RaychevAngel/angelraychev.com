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

def b1740 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 84 265 146 96 65 160 416), lower := (rows 7 42 84 265 146 96 65 128 256), losses := [] }

theorem u1740 : Upper (D 7) (R 7) [6,40,80,257,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1740 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1741 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 265 146 96 96 129 385), lower := (rows 7 42 84 265 146 96 96 128 256), losses := [] }

theorem u1741 : Upper (D 7) (R 7) [6,40,80,257,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1741 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1742 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 265 146 96 192 161 289), lower := (rows 7 42 84 265 146 96 192 128 256), losses := [] }

theorem u1742 : Upper (D 7) (R 7) [6,40,80,257,130,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1742 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1743 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 265 146 160 65 224 352), lower := (rows 7 42 84 265 146 160 65 128 256), losses := [] }

theorem u1743 : Upper (D 7) (R 7) [6,40,80,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1743 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1744 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,7),(2,0),(2,1),(3,1)], upper := (rows 7 42 84 265 146 160 96 193 321), lower := (rows 7 42 84 265 146 160 96 128 256), losses := [{ target := 7, region := (rows 17 2 20 29 16 32 98 0 277), good := (rows 335 106 349 265 351 96 96 0 256) }] }

theorem u1744 : Upper (D 7) (R 7) [6,40,80,257,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1744 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1745 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 0, region := 392, targets := 32 },{ cop := 0, region := 392, targets := 64 }], pairs := [(3,5),(3,6),(4,0),(4,6)], upper := (rows 7 42 84 265 176 96 65 130 386), lower := (rows 7 42 84 265 176 96 65 128 256), losses := [] }

theorem u1745 : Upper (D 7) (R 7) [6,40,80,257,160,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1745 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1746 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 66 },{ cop := 3, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(3,1),(3,6)], upper := (rows 7 42 84 265 176 96 66 129 385), lower := (rows 7 42 84 265 176 96 66 128 256), losses := [] }

theorem u1746 : Upper (D 7) (R 7) [6,40,80,257,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1746 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1747 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 52, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,1)], upper := (rows 7 42 84 265 176 96 192 131 259), lower := (rows 7 42 84 265 176 96 192 128 256), losses := [] }

theorem u1747 : Upper (D 7) (R 7) [6,40,80,257,160,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1747 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1748 : PairBound 9 := { available := 160, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 266 145 96 65 160 416), lower := (rows 7 42 84 266 145 96 65 128 256), losses := [] }

theorem u1748 : Upper (D 7) (R 7) [6,40,80,258,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1748 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1749 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 266 145 96 96 129 385), lower := (rows 7 42 84 266 145 96 96 128 256), losses := [] }

theorem u1749 : Upper (D 7) (R 7) [6,40,80,258,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1749 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1750 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 0, region := 244, targets := 2 }], pairs := [(0,7),(1,7),(2,1),(3,7)], upper := (rows 7 42 84 266 145 96 192 161 289), lower := (rows 7 42 84 266 145 96 192 128 256), losses := [] }

theorem u1750 : Upper (D 7) (R 7) [6,40,80,258,129,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1750 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1751 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 2, region := 426, targets := 1 }], pairs := [(1,0),(2,1),(3,0),(4,1)], upper := (rows 7 42 84 266 145 160 65 224 352), lower := (rows 7 42 84 266 145 160 65 128 256), losses := [] }

theorem u1751 : Upper (D 7) (R 7) [6,40,80,258,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1751 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1752 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 244, targets := 2 },{ cop := 4, region := 100, targets := 1 }], pairs := [(2,0),(2,1),(3,7),(4,1)], upper := (rows 7 42 84 266 145 160 96 193 321), lower := (rows 7 42 84 266 145 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 16 32 98 0 257), good := (rows 335 106 84 330 281 96 96 0 256) }] }

theorem u1752 : Upper (D 7) (R 7) [6,40,80,258,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1752 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1753 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 2, region := 426, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 7 42 84 328 49 160 65 130 386), lower := (rows 7 42 84 328 49 160 65 128 256), losses := [] }

theorem u1753 : Upper (D 7) (R 7) [6,40,80,320,33,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1753 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1754 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 176, targets := 2 }], pairs := [(0,7),(2,7),(4,1),(4,7)], upper := (rows 7 42 84 328 49 160 66 129 385), lower := (rows 7 42 84 328 49 160 66 128 256), losses := [] }

theorem u1754 : Upper (D 7) (R 7) [6,40,80,320,33,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1754 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1755 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 456, targets := 32 },{ cop := 0, region := 176, targets := 64 }], pairs := [(1,0),(2,0),(3,5),(4,6)], upper := (rows 7 42 84 328 49 160 192 131 259), lower := (rows 7 42 84 328 49 160 192 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 224 224 128 256), good := (rows 6 106 116 362 116 224 224 224 256) }] }

theorem u1755 : Upper (D 7) (R 7) [6,40,80,320,33,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1755 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1756 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(3,0),(4,1),(4,6)], upper := (rows 7 42 84 328 145 33 66 160 416), lower := (rows 7 42 84 328 145 33 66 128 256), losses := [] }

theorem u1756 : Upper (D 7) (R 7) [6,40,80,320,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1756 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1757 : PairBound 9 := { available := 130, camps := [{ cop := 4, region := 100, targets := 130 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,7),(3,0)], upper := (rows 7 42 84 328 145 33 96 130 386), lower := (rows 7 42 84 328 145 33 96 128 256), losses := [] }

theorem u1757 : Upper (D 7) (R 7) [6,40,80,320,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1757 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1758 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 328 145 33 192 162 290), lower := (rows 7 42 84 328 145 33 192 128 256), losses := [] }

theorem u1758 : Upper (D 7) (R 7) [6,40,80,320,129,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1758 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1759 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 4, region := 68, targets := 160 }], pairs := [(1,0),(2,5),(2,7),(3,0)], upper := (rows 7 42 84 328 145 160 65 162 290), lower := (rows 7 42 84 328 145 160 65 128 256), losses := [] }

theorem u1759 : Upper (D 7) (R 7) [6,40,80,320,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1759 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1760 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 176, targets := 66 }], pairs := [(2,0),(3,1),(4,1),(4,6)], upper := (rows 7 42 84 328 145 160 66 161 289), lower := (rows 7 42 84 328 145 160 66 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 176 67 128 256), good := (rows 70 106 116 328 244 160 66 160 256) },{ target := 1, region := (rows 1 0 4 12 17 181 64 145 273), good := (rows 445 40 508 328 433 160 64 160 256) }] }

theorem u1760 : Upper (D 7) (R 7) [6,40,80,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1760 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1761 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 144, targets := 32 },{ cop := 0, region := 144, targets := 64 }], pairs := [(2,0),(2,1),(4,5),(4,6)], upper := (rows 7 42 84 328 145 160 96 131 259), lower := (rows 7 42 84 328 145 160 96 128 256), losses := [] }

theorem u1761 : Upper (D 7) (R 7) [6,40,80,320,129,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1761 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1762 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 4, region := 69, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 84 328 146 33 65 160 416), lower := (rows 7 42 84 328 146 33 65 128 256), losses := [] }

theorem u1762 : Upper (D 7) (R 7) [6,40,80,320,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1762 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1763 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(0,7),(2,7),(3,1),(4,5)], upper := (rows 7 42 84 328 146 33 96 129 385), lower := (rows 7 42 84 328 146 33 96 128 256), losses := [] }

theorem u1763 : Upper (D 7) (R 7) [6,40,80,320,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1763 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1764 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 328 146 33 192 161 289), lower := (rows 7 42 84 328 146 33 192 128 256), losses := [] }

theorem u1764 : Upper (D 7) (R 7) [6,40,80,320,130,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1764 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1765 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 160 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 328 146 160 65 161 289), lower := (rows 7 42 84 328 146 160 65 128 256), losses := [] }

theorem u1765 : Upper (D 7) (R 7) [6,40,80,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1765 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1766 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 100, targets := 3 },{ cop := 0, region := 488, targets := 2 },{ cop := 0, region := 144, targets := 32 }], pairs := [(2,0),(2,1),(3,1),(4,5)], upper := (rows 7 42 84 328 146 160 96 129 257), lower := (rows 7 42 84 328 146 160 96 128 256), losses := [] }

theorem u1766 : Upper (D 7) (R 7) [6,40,80,320,130,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1766 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1767 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 144, targets := 65 },{ cop := 0, region := 456, targets := 32 }], pairs := [(3,0),(3,5),(4,0),(4,6)], upper := (rows 7 42 84 328 176 33 65 130 386), lower := (rows 7 42 84 328 176 33 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 50 32 64 131 259), good := (rows 406 442 92 328 176 432 456 128 256) }] }

theorem u1767 : Upper (D 7) (R 7) [6,40,80,320,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1767 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1768 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 176, targets := 66 },{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(3,5),(4,1),(4,6)], upper := (rows 7 42 84 328 176 33 66 129 385), lower := (rows 7 42 84 328 176 33 66 128 256), losses := [{ target := 1, region := (rows 1 0 68 8 51 33 64 161 289), good := (rows 437 440 84 332 432 433 84 128 256) }] }

theorem u1768 : Upper (D 7) (R 7) [6,40,80,320,160,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1768 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1769 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 299, targets := 128 },{ cop := 4, region := 68, targets := 1 }], pairs := [(0,7),(1,7),(2,0),(3,7)], upper := (rows 7 42 84 328 176 33 192 131 259), lower := (rows 7 42 84 328 176 33 192 128 256), losses := [] }

theorem u1769 : Upper (D 7) (R 7) [6,40,80,320,160,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1769 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1770 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,0),(3,0),(3,1)], upper := (rows 7 42 84 392 145 33 66 224 352), lower := (rows 7 42 84 392 145 33 66 128 256), losses := [{ target := 0, region := (rows 0 34 20 107 16 32 99 162 290), good := (rows 462 490 92 392 220 490 458 128 256) },{ target := 1, region := (rows 1 0 4 13 17 49 64 132 260), good := (rows 445 40 508 392 185 57 64 128 256) }] }

theorem u1770 : Upper (D 7) (R 7) [6,40,80,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1770 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1771 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 100, targets := 130 },{ cop := 5, region := 458, targets := 1 }], pairs := [(1,0),(2,1),(2,7),(3,0)], upper := (rows 7 42 84 392 145 33 96 194 322), lower := (rows 7 42 84 392 145 33 96 128 256), losses := [] }

theorem u1771 : Upper (D 7) (R 7) [6,40,80,384,129,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1771 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1772 : PairBound 9 := { available := 34, camps := [{ cop := 5, region := 394, targets := 65 }], pairs := [(1,0),(1,6),(3,0),(3,6)], upper := (rows 7 42 84 392 145 96 65 162 290), lower := (rows 7 42 84 392 145 96 65 128 256), losses := [] }

theorem u1772 : Upper (D 7) (R 7) [6,40,80,384,129,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1772 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1773 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 98, targets := 129 }], pairs := [(1,0),(1,7),(2,0),(3,1)], upper := (rows 7 42 84 392 145 96 66 161 289), lower := (rows 7 42 84 392 145 96 66 128 256), losses := [{ target := 0, region := (rows 0 10 20 8 16 127 75 128 256), good := (rows 102 106 116 490 244 96 98 128 256) },{ target := 1, region := (rows 1 0 4 25 17 100 64 129 257), good := (rows 445 40 124 392 409 96 96 128 256) }] }

theorem u1773 : Upper (D 7) (R 7) [6,40,80,384,129,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1773 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1774 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 392 145 96 96 131 259), lower := (rows 7 42 84 392 145 96 96 128 256), losses := [] }

theorem u1774 : Upper (D 7) (R 7) [6,40,80,384,129,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1774 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1775 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 392 146 33 65 224 352), lower := (rows 7 42 84 392 146 33 65 128 256), losses := [] }

theorem u1775 : Upper (D 7) (R 7) [6,40,80,384,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1775 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1776 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 101, targets := 128 },{ cop := 0, region := 488, targets := 2 }], pairs := [(0,7),(2,0),(2,7),(3,1)], upper := (rows 7 42 84 392 146 33 96 193 321), lower := (rows 7 42 84 392 146 33 96 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 32 98 128 256), good := (rows 70 106 84 392 214 96 96 128 256) }] }

theorem u1776 : Upper (D 7) (R 7) [6,40,80,384,130,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1776 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1777 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 32 },{ cop := 4, region := 69, targets := 128 }], pairs := [(0,5),(0,7),(2,5),(2,7)], upper := (rows 7 42 84 392 146 96 65 161 289), lower := (rows 7 42 84 392 146 96 65 128 256), losses := [] }

theorem u1777 : Upper (D 7) (R 7) [6,40,80,384,130,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1777 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1778 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 84 392 146 96 96 129 257), lower := (rows 7 42 84 392 146 96 96 128 256), losses := [] }

theorem u1778 : Upper (D 7) (R 7) [6,40,80,384,130,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1778 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1779 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 456, targets := 32 }], pairs := [(2,1),(2,5),(2,7),(3,5)], upper := (rows 7 42 84 392 176 33 65 194 322), lower := (rows 7 42 84 392 176 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 20 8 16 97 97 128 256), good := (rows 101 104 116 392 244 97 97 128 256) },{ target := 5, region := (rows 1 2 20 107 16 0 97 131 259), good := (rows 463 458 92 392 220 457 457 128 256) },{ target := 7, region := (rows 1 2 20 8 16 97 97 0 259), good := (rows 359 362 116 264 116 353 353 0 256) }] }

theorem u1779 : Upper (D 7) (R 7) [6,40,80,384,160,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1779 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1780 : Route 9 := (fun mask => (mask,id))

def c1780 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1780 : Upper (D 7) (R 7) [6,40,80,384,160,1,2] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,1,2] 13 (by decide) (choices 1) [1,64] r1780 c1780
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u76
  · exact u77

def r1781 : Route 9 := (fun mask => (mask,id))

def c1781 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1781 : Upper (D 7) (R 7) [6,40,80,384,160,64,1] 13 := by
  apply FastRouting.sound _ _ [6,40,80,384,160,64,1] 13 (by decide) (choices 1) [1,2] r1781 c1781
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u78
  · exact u79

def b1782 : PairBound 9 := { available := 1, camps := [{ cop := 3, region := 118, targets := 1 },{ cop := 0, region := 392, targets := 2 }], pairs := [(1,0),(2,0),(3,1),(4,0)], upper := (rows 7 42 84 392 176 96 66 129 257), lower := (rows 7 42 84 392 176 96 66 128 256), losses := [] }

theorem u1782 : Upper (D 7) (R 7) [6,40,80,384,160,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1782 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1783 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 274 160 65 192 448), lower := (rows 7 42 100 25 274 160 65 128 256), losses := [] }

theorem u1783 : Upper (D 7) (R 7) [6,40,96,17,258,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1783 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1784 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 25 274 160 192 193 321), lower := (rows 7 42 100 25 274 160 192 128 256), losses := [] }

theorem u1784 : Upper (D 7) (R 7) [6,40,96,17,258,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1784 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1785 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 336 160 65 130 386), lower := (rows 7 42 100 25 336 160 65 128 256), losses := [] }

theorem u1785 : Upper (D 7) (R 7) [6,40,96,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1785 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1786 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 25 336 160 66 129 385), lower := (rows 7 42 100 25 336 160 66 128 256), losses := [] }

theorem u1786 : Upper (D 7) (R 7) [6,40,96,17,320,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1786 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1787 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 25 336 160 192 131 259), lower := (rows 7 42 100 25 336 160 192 128 256), losses := [] }

theorem u1787 : Upper (D 7) (R 7) [6,40,96,17,320,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1787 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1788 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 100 137 82 288 65 144 400), lower := (rows 7 42 100 137 82 288 65 128 256), losses := [] }

theorem u1788 : Upper (D 7) (R 7) [6,40,96,129,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1788 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1789 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7)], upper := (rows 7 42 100 137 82 288 80 129 385), lower := (rows 7 42 100 137 82 288 80 128 256), losses := [] }

theorem u1789 : Upper (D 7) (R 7) [6,40,96,129,66,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1789 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1790 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 4, region := 293, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 137 82 288 192 145 273), lower := (rows 7 42 100 137 82 288 192 128 256), losses := [] }

theorem u1790 : Upper (D 7) (R 7) [6,40,96,129,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1790 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1791 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 137 208 288 65 146 274), lower := (rows 7 42 100 137 208 288 65 128 256), losses := [] }

theorem u1791 : Upper (D 7) (R 7) [6,40,96,129,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1791 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1792 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 216, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(3,5),(4,5)], upper := (rows 7 42 100 137 208 288 66 145 273), lower := (rows 7 42 100 137 208 288 66 128 256), losses := [] }

theorem u1792 : Upper (D 7) (R 7) [6,40,96,129,192,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1792 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1793 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 139, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 42 100 137 208 288 80 131 259), lower := (rows 7 42 100 137 208 288 80 128 256), losses := [] }

theorem u1793 : Upper (D 7) (R 7) [6,40,96,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1793 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1794 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 100 152 274 33 65 192 448), lower := (rows 7 42 100 152 274 33 65 128 256), losses := [] }

theorem u1794 : Upper (D 7) (R 7) [6,40,96,144,258,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1794 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1795 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 0, region := 228, targets := 2 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 42 100 152 274 33 192 193 321), lower := (rows 7 42 100 152 274 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 200 128 256), good := (rows 6 110 100 216 278 32 192 192 256) }] }

theorem u1795 : Upper (D 7) (R 7) [6,40,96,144,258,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1795 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1796 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 100 152 336 33 65 130 386), lower := (rows 7 42 100 152 336 33 65 128 256), losses := [] }

theorem u1796 : Upper (D 7) (R 7) [6,40,96,144,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1796 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1797 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 152 336 33 66 129 385), lower := (rows 7 42 100 152 336 33 66 128 256), losses := [] }

theorem u1797 : Upper (D 7) (R 7) [6,40,96,144,320,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1797 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1798 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 472, targets := 32 }], pairs := [(2,0),(2,1),(3,5),(4,5)], upper := (rows 7 42 100 152 336 33 192 131 259), lower := (rows 7 42 100 152 336 33 192 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 16 32 200 128 256), good := (rows 6 110 100 216 336 32 192 192 256) },{ target := 1, region := (rows 1 0 6 8 16 33 200 128 256), good := (rows 37 108 100 216 336 33 192 192 256) }] }

theorem u1798 : Upper (D 7) (R 7) [6,40,96,144,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1798 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1799 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 265 82 160 65 144 400), lower := (rows 7 42 100 265 82 160 65 128 256), losses := [] }

theorem u1799 : Upper (D 7) (R 7) [6,40,96,257,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1799 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1799
end Delivery.IrregularNine14.P07
