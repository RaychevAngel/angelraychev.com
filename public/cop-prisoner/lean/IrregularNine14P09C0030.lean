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

def b1800 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,6),(0,7),(0,8),(3,0)], upper := (rows 35 194 13 328 304 33 80 132 388), lower := (rows 35 194 13 328 304 33 80 128 256), losses := [] }

theorem u1800 : Upper (D 9) (R 9) [34,192,9,320,288,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1800 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 304 33 192 148 276), lower := (rows 35 194 13 328 304 33 192 128 256), losses := [] }

theorem u1801 : Upper (D 9) (R 9) [34,192,9,320,288,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1801 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 432, targets := 65 },{ cop := 4, region := 195, targets := 256 }], pairs := [(0,8),(1,8),(4,0),(4,6)], upper := (rows 35 194 13 328 304 36 65 144 400), lower := (rows 35 194 13 328 304 36 65 128 256), losses := [] }

theorem u1802 : Upper (D 9) (R 9) [34,192,9,320,288,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1802 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 35 194 13 328 304 36 80 129 385), lower := (rows 35 194 13 328 304 36 80 128 256), losses := [] }

theorem u1803 : Upper (D 9) (R 9) [34,192,9,320,288,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1803 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 13 328 304 36 192 145 273), lower := (rows 35 194 13 328 304 36 192 128 256), losses := [] }

theorem u1804 : Upper (D 9) (R 9) [34,192,9,320,288,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1804 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(4,6)], upper := (rows 35 194 13 328 400 33 68 176 304), lower := (rows 35 194 13 328 400 33 68 128 256), losses := [] }

theorem u1805 : Upper (D 9) (R 9) [34,192,9,320,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1805 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 13 328 400 33 80 164 292), lower := (rows 35 194 13 328 400 33 80 128 256), losses := [] }

theorem u1806 : Upper (D 9) (R 9) [34,192,9,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1806 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 2, region := 400, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(4,0),(4,5)], upper := (rows 35 194 13 328 400 33 96 148 276), lower := (rows 35 194 13 328 400 33 96 128 256), losses := [] }

theorem u1807 : Upper (D 9) (R 9) [34,192,9,320,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1807 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 432, targets := 65 }], pairs := [(1,0),(3,0),(4,0),(4,6)], upper := (rows 35 194 13 328 400 36 65 176 304), lower := (rows 35 194 13 328 400 36 65 128 256), losses := [{ target := 0, region := (rows 0 66 4 72 117 36 64 165 293), good := (rows 434 218 444 346 400 436 474 128 256) }] }

theorem u1808 : Upper (D 9) (R 9) [34,192,9,320,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1808 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0)], upper := (rows 35 194 13 328 400 36 80 161 289), lower := (rows 35 194 13 328 400 36 80 128 256), losses := [] }

theorem u1809 : Upper (D 9) (R 9) [34,192,9,320,384,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1809 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1810 : Route 9 := (fun mask => (mask,id))

def c1810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1810 : Upper (D 9) (R 9) [34,192,9,320,384,4,32] 13 := by
  apply FastRouting.sound _ _ [34,192,9,320,384,4,32] 13 (by decide) (choices 1) [1,16] r1810 c1810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u97
  · exact u98

def b1811 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 2, region := 432, targets := 65 }], pairs := [(2,7),(3,7),(4,0),(4,6)], upper := (rows 35 194 13 328 400 48 65 164 292), lower := (rows 35 194 13 328 400 48 65 128 256), losses := [] }

theorem u1811 : Upper (D 9) (R 9) [34,192,9,320,384,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1811 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 1, region := 305, targets := 64 }], pairs := [(0,6),(2,7),(3,7)], upper := (rows 35 194 13 328 400 48 68 161 289), lower := (rows 35 194 13 328 400 48 68 128 256), losses := [] }

theorem u1812 : Upper (D 9) (R 9) [34,192,9,320,384,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1812 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 332, targets := 128 },{ cop := 4, region := 106, targets := 1 }], pairs := [(1,0),(2,7),(3,0),(3,7)], upper := (rows 35 194 13 328 400 48 96 133 261), lower := (rows 35 194 13 328 400 48 96 128 256), losses := [] }

theorem u1813 : Upper (D 9) (R 9) [34,192,9,320,384,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1813 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 3, region := 438, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 73 176 288 65 388 260), lower := (rows 35 194 28 73 176 288 65 128 256), losses := [] }

theorem u1814 : Upper (D 9) (R 9) [34,192,24,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1814 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 73 176 288 68 385 257), lower := (rows 35 194 28 73 176 288 68 128 256), losses := [] }

theorem u1815 : Upper (D 9) (R 9) [34,192,24,65,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1815 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(1,0),(1,5),(2,6),(4,0),(4,6)], upper := (rows 35 194 28 73 176 288 320 133 261), lower := (rows 35 194 28 73 176 288 320 128 256), losses := [{ target := 0, region := (rows 0 18 4 8 18 352 352 128 256), good := (rows 114 242 30 104 242 352 352 128 352) },{ target := 5, region := (rows 1 18 4 9 16 0 352 128 256), good := (rows 75 194 30 73 210 320 320 128 320) }] }

theorem u1816 : Upper (D 9) (R 9) [34,192,24,65,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1816 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 108, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 28 73 273 36 96 384 384), lower := (rows 35 194 28 73 273 36 96 128 256), losses := [] }

theorem u1817 : Upper (D 9) (R 9) [34,192,24,65,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1817 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 273 36 192 416 288), lower := (rows 35 194 28 73 273 36 192 128 256), losses := [] }

theorem u1818 : Upper (D 9) (R 9) [34,192,24,65,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1818 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 76, targets := 32 }], pairs := [(2,5),(2,6),(3,5),(4,6)], upper := (rows 35 194 28 73 273 36 320 160 416), lower := (rows 35 194 28 73 273 36 320 128 256), losses := [] }

theorem u1819 : Upper (D 9) (R 9) [34,192,24,65,257,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1819 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 76, targets := 288 }], pairs := [(2,5),(2,8),(3,5),(3,8)], upper := (rows 35 194 28 73 273 288 68 160 416), lower := (rows 35 194 28 73 273 288 68 128 256), losses := [] }

theorem u1820 : Upper (D 9) (R 9) [34,192,24,65,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1820 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 194 28 73 273 288 96 132 388), lower := (rows 35 194 28 73 273 288 96 128 256), losses := [] }

theorem u1821 : Upper (D 9) (R 9) [34,192,24,65,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1821 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 73 273 288 192 164 292), lower := (rows 35 194 28 73 273 288 192 128 256), losses := [] }

theorem u1822 : Upper (D 9) (R 9) [34,192,24,65,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1822 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 73 400 36 65 416 288), lower := (rows 35 194 28 73 400 36 65 128 256), losses := [] }

theorem u1823 : Upper (D 9) (R 9) [34,192,24,65,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1823 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 73 400 36 96 385 257), lower := (rows 35 194 28 73 400 36 96 128 256), losses := [] }

theorem u1824 : Upper (D 9) (R 9) [34,192,24,65,384,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1824 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 66, targets := 33 }], pairs := [(1,0),(1,5),(2,6),(4,6)], upper := (rows 35 194 28 73 400 36 320 161 289), lower := (rows 35 194 28 73 400 36 320 128 256), losses := [] }

theorem u1825 : Upper (D 9) (R 9) [34,192,24,65,384,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1825 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 72, targets := 416 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,0),(3,5),(3,7),(3,8)], upper := (rows 35 194 28 73 400 288 65 164 292), lower := (rows 35 194 28 73 400 288 65 128 256), losses := [] }

theorem u1826 : Upper (D 9) (R 9) [34,192,24,65,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1826 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 297, targets := 128 }], pairs := [(0,6),(0,7),(3,7),(4,6)], upper := (rows 35 194 28 73 400 288 68 161 289), lower := (rows 35 194 28 73 400 288 68 128 256), losses := [] }

theorem u1827 : Upper (D 9) (R 9) [34,192,24,65,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1827 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 406, targets := 32 },{ cop := 0, region := 72, targets := 384 }], pairs := [(1,5),(2,5),(3,7),(3,8),(4,5)], upper := (rows 35 194 28 73 400 288 96 133 261), lower := (rows 35 194 28 73 400 288 96 128 256), losses := [] }

theorem u1828 : Upper (D 9) (R 9) [34,192,24,65,384,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1828 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 79, targets := 256 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 76 176 288 65 385 257), lower := (rows 35 194 28 76 176 288 65 128 256), losses := [] }

theorem u1829 : Upper (D 9) (R 9) [34,192,24,68,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1829 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 0, region := 450, targets := 32 },{ cop := 0, region := 144, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(4,6),(4,8)], upper := (rows 35 194 28 76 176 288 320 129 257), lower := (rows 35 194 28 76 176 288 320 128 256), losses := [] }

theorem u1830 : Upper (D 9) (R 9) [34,192,24,68,160,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1830 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 288, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 76 400 33 65 416 288), lower := (rows 35 194 28 76 400 33 65 128 256), losses := [] }

theorem u1831 : Upper (D 9) (R 9) [34,192,24,68,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1831 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 28 76 400 33 96 385 257), lower := (rows 35 194 28 76 400 33 96 128 256), losses := [] }

theorem u1832 : Upper (D 9) (R 9) [34,192,24,68,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1832 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5),(3,0)], upper := (rows 35 194 28 76 400 33 320 161 289), lower := (rows 35 194 28 76 400 33 320 128 256), losses := [] }

theorem u1833 : Upper (D 9) (R 9) [34,192,24,68,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1833 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 384, camps := [{ cop := 4, region := 108, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 28 104 273 36 65 384 384), lower := (rows 35 194 28 104 273 36 65 128 256), losses := [] }

theorem u1834 : Upper (D 9) (R 9) [34,192,24,96,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1834 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 104 273 36 192 385 257), lower := (rows 35 194 28 104 273 36 192 128 256), losses := [] }

theorem u1835 : Upper (D 9) (R 9) [34,192,24,96,257,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1835 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 108, targets := 129 }], pairs := [(2,0),(2,7),(3,0),(3,7)], upper := (rows 35 194 28 104 273 36 320 129 385), lower := (rows 35 194 28 104 273 36 320 128 256), losses := [] }

theorem u1836 : Upper (D 9) (R 9) [34,192,24,96,257,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1836 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 72, targets := 384 },{ cop := 4, region := 108, targets := 128 }], pairs := [(1,5),(1,8),(2,7),(3,7),(3,8)], upper := (rows 35 194 28 104 273 288 65 132 388), lower := (rows 35 194 28 104 273 288 65 128 256), losses := [{ target := 5, region := (rows 1 6 4 8 16 0 81 132 260), good := (rows 67 194 478 72 337 256 65 128 256) },{ target := 8, region := (rows 1 22 20 9 16 32 81 148 0), good := (rows 107 194 222 104 223 32 73 128 0) }] }

theorem u1837 : Upper (D 9) (R 9) [34,192,24,96,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1837 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 108, targets := 129 }], pairs := [(2,0),(2,7),(3,0),(3,7)], upper := (rows 35 194 28 104 273 288 68 129 385), lower := (rows 35 194 28 104 273 288 68 128 256), losses := [] }

theorem u1838 : Upper (D 9) (R 9) [34,192,24,96,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1838 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 104 273 288 192 133 261), lower := (rows 35 194 28 104 273 288 192 128 256), losses := [] }

theorem u1839 : Upper (D 9) (R 9) [34,192,24,96,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1839 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1840 : Route 9 := (fun mask => (mask,id))

def c1840 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1840 : Upper (D 9) (R 9) [34,192,24,96,384,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,24,96,384,256,1] 13 (by decide) (choices 1) [1,4] r1840 c1840
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u99
  · exact u100

def b1841 : PairBound 9 := { available := 1, camps := [{ cop := 4, region := 110, targets := 1 },{ cop := 1, region := 289, targets := 64 }], pairs := [(0,6),(1,0),(2,0),(3,0)], upper := (rows 35 194 28 104 400 288 68 129 257), lower := (rows 35 194 28 104 400 288 68 128 256), losses := [] }

theorem u1841 : Upper (D 9) (R 9) [34,192,24,96,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1841 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 84, targets := 33 }], pairs := [(2,0),(2,5),(4,0),(4,5)], upper := (rows 35 194 28 265 336 33 68 160 416), lower := (rows 35 194 28 265 336 33 68 128 256), losses := [] }

theorem u1842 : Upper (D 9) (R 9) [34,192,24,257,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1842 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 3, region := 116, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(0,8),(2,7),(4,7)], upper := (rows 35 194 28 265 336 33 96 132 388), lower := (rows 35 194 28 265 336 33 96 128 256), losses := [] }

theorem u1843 : Upper (D 9) (R 9) [34,192,24,257,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1843 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 265 336 33 192 164 292), lower := (rows 35 194 28 265 336 33 192 128 256), losses := [] }

theorem u1844 : Upper (D 9) (R 9) [34,192,24,257,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1844 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 227, targets := 256 },{ cop := 3, region := 84, targets := 32 }], pairs := [(0,8),(1,8),(2,5),(4,5)], upper := (rows 35 194 28 265 336 36 65 160 416), lower := (rows 35 194 28 265 336 36 65 128 256), losses := [] }

theorem u1845 : Upper (D 9) (R 9) [34,192,24,257,320,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1845 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 116, targets := 129 }], pairs := [(2,0),(2,7),(4,0),(4,7)], upper := (rows 35 194 28 265 336 36 96 129 385), lower := (rows 35 194 28 265 336 36 96 128 256), losses := [] }

theorem u1846 : Upper (D 9) (R 9) [34,192,24,257,320,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1846 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 265 336 36 192 161 289), lower := (rows 35 194 28 265 336 36 192 128 256), losses := [] }

theorem u1847 : Upper (D 9) (R 9) [34,192,24,257,320,4,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1847 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 28 296 336 33 65 132 388), lower := (rows 35 194 28 296 336 33 65 128 256), losses := [{ target := 0, region := (rows 0 82 69 41 82 32 64 247 375), good := (rows 446 470 414 424 470 428 478 128 256) }] }

theorem u1848 : Upper (D 9) (R 9) [34,192,24,288,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1848 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 84, targets := 161 }], pairs := [(2,0),(2,5),(2,7),(4,0)], upper := (rows 35 194 28 296 336 33 68 129 385), lower := (rows 35 194 28 296 336 33 68 128 256), losses := [] }

theorem u1849 : Upper (D 9) (R 9) [34,192,24,288,320,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1849 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 28 296 336 33 192 133 261), lower := (rows 35 194 28 296 336 33 192 128 256), losses := [] }

theorem u1850 : Upper (D 9) (R 9) [34,192,24,288,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1850 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 384 },{ cop := 1, region := 33, targets := 64 },{ cop := 2, region := 227, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 28 328 400 33 65 164 292), lower := (rows 35 194 28 328 400 33 65 128 256), losses := [{ target := 0, region := (rows 0 66 78 72 113 32 64 129 257), good := (rows 438 222 28 350 400 432 478 128 256) }] }

theorem u1851 : Upper (D 9) (R 9) [34,192,24,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1851 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 78, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 28 328 400 33 68 161 289), lower := (rows 35 194 28 328 400 33 68 128 256), losses := [] }

theorem u1852 : Upper (D 9) (R 9) [34,192,24,320,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1852 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

theorem m1853_1 : Upper (D 9) (R 9) [34,192,24,320,384,1,32,1] 13 :=
  permutation_upper _ _ _ [34,192,24,320,384,1,1,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u101

theorem m1853_4 : Upper (D 9) (R 9) [34,192,24,320,384,1,32,4] 13 :=
  permutation_upper _ _ _ [34,192,24,320,384,1,4,32] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 7 | 7 => 6 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u102

def r1853 : Route 9 := (fun mask => (mask,id))

def c1853 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1853 : Upper (D 9) (R 9) [34,192,24,320,384,1,32] 13 := by
  apply FastRouting.sound _ _ [34,192,24,320,384,1,32] 13 (by decide) (choices 1) [1,4] r1853 c1853
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1853_1
  · exact m1853_4

def b1854 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 145 288 68 400 272), lower := (rows 35 194 44 73 145 288 68 128 256), losses := [] }

theorem u1854 : Upper (D 9) (R 9) [34,192,40,65,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1854 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 74, targets := 288 }], pairs := [(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 194 44 73 145 288 80 388 260), lower := (rows 35 194 44 73 145 288 80 128 256), losses := [] }

theorem u1855 : Upper (D 9) (R 9) [34,192,40,65,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1855 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 20, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 4, region := 364, targets := 128 }], pairs := [(2,0),(2,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 44 73 145 288 320 148 276), lower := (rows 35 194 44 73 145 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 352 352 128 256), good := (rows 98 226 108 108 144 352 352 128 352) }] }

theorem u1856 : Upper (D 9) (R 9) [34,192,40,65,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1856 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 148 288 65 400 272), lower := (rows 35 194 44 73 148 288 65 128 256), losses := [] }

theorem u1857 : Upper (D 9) (R 9) [34,192,40,65,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1857 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 44 73 148 288 80 385 257), lower := (rows 35 194 44 73 148 288 80 128 256), losses := [] }

theorem u1858 : Upper (D 9) (R 9) [34,192,40,65,132,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1858 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(0,6),(2,0),(2,6),(3,5),(4,6)], upper := (rows 35 194 44 73 148 288 320 145 273), lower := (rows 35 194 44 73 148 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 352 352 128 256), good := (rows 98 226 108 108 148 352 352 128 352) },{ target := 5, region := (rows 1 2 4 9 16 0 352 128 256), good := (rows 75 194 76 73 148 320 320 128 320) },{ target := 6, region := (rows 3 2 12 8 28 364 0 136 264), good := (rows 35 163 444 445 180 288 288 128 288) }] }

theorem u1859 : Upper (D 9) (R 9) [34,192,40,65,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1859 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P09
