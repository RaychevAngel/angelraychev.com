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

def b1800 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 7 42 100 265 82 160 80 129 385), lower := (rows 7 42 100 265 82 160 80 128 256), losses := [] }

theorem u1800 : Upper (D 7) (R 7) [6,40,96,257,66,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1800 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 265 82 160 192 145 273), lower := (rows 7 42 100 265 82 160 192 128 256), losses := [] }

theorem u1801 : Upper (D 7) (R 7) [6,40,96,257,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1801 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 265 145 160 66 208 336), lower := (rows 7 42 100 265 145 160 66 128 256), losses := [] }

theorem u1802 : Upper (D 7) (R 7) [6,40,96,257,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1802 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 100 265 145 160 80 194 322), lower := (rows 7 42 100 265 145 160 80 128 256), losses := [] }

theorem u1803 : Upper (D 7) (R 7) [6,40,96,257,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1803 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 265 146 160 65 208 336), lower := (rows 7 42 100 265 146 160 65 128 256), losses := [] }

theorem u1804 : Upper (D 7) (R 7) [6,40,96,257,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1804 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 100 265 146 160 80 193 321), lower := (rows 7 42 100 265 146 160 80 128 256), losses := [] }

theorem u1805 : Upper (D 7) (R 7) [6,40,96,257,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1805 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 85, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(2,7),(3,5),(4,7)], upper := (rows 7 42 100 280 82 160 65 129 385), lower := (rows 7 42 100 280 82 160 65 128 256), losses := [] }

theorem u1806 : Upper (D 7) (R 7) [6,40,96,272,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1806 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 100 280 82 160 192 129 257), lower := (rows 7 42 100 280 82 160 192 128 256), losses := [] }

theorem u1807 : Upper (D 7) (R 7) [6,40,96,272,66,128,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1807 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 192, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 100 280 146 33 65 192 448), lower := (rows 7 42 100 280 146 33 65 128 256), losses := [] }

theorem u1808 : Upper (D 7) (R 7) [6,40,96,272,130,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1808 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1809 : Route 9 := (fun mask => (mask,id))

def c1809 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1809 : Upper (D 7) (R 7) [6,40,96,272,130,1,128] 13 := by
  apply FastRouting.sound _ _ [6,40,96,272,130,1,128] 13 (by decide) (choices 1) [1,64] r1809 c1809
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u80
  · exact u81

def b1810 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 100 280 208 33 65 130 386), lower := (rows 7 42 100 280 208 33 65 128 256), losses := [] }

theorem u1810 : Upper (D 7) (R 7) [6,40,96,272,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1810 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 280 208 33 66 129 385), lower := (rows 7 42 100 280 208 33 66 128 256), losses := [] }

theorem u1811 : Upper (D 7) (R 7) [6,40,96,272,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1811 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 3, camps := [{ cop := 4, region := 303, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(3,7)], upper := (rows 7 42 100 280 208 33 192 131 259), lower := (rows 7 42 100 280 208 33 192 128 256), losses := [] }

theorem u1812 : Upper (D 7) (R 7) [6,40,96,272,192,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1812 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 328 145 160 65 146 274), lower := (rows 7 42 100 328 145 160 65 128 256), losses := [] }

theorem u1813 : Upper (D 7) (R 7) [6,40,96,320,129,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1813 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 144, targets := 66 },{ cop := 0, region := 472, targets := 32 }], pairs := [(3,5),(4,1),(4,5),(4,6)], upper := (rows 7 42 100 328 145 160 66 145 273), lower := (rows 7 42 100 328 145 160 66 128 256), losses := [] }

theorem u1814 : Upper (D 7) (R 7) [6,40,96,320,129,128,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1814 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 100 328 145 160 80 131 259), lower := (rows 7 42 100 328 145 160 80 128 256), losses := [] }

theorem u1815 : Upper (D 7) (R 7) [6,40,96,320,129,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1815 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 1, region := 69, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5)], upper := (rows 7 42 100 328 146 160 65 145 273), lower := (rows 7 42 100 328 146 160 65 128 256), losses := [] }

theorem u1816 : Upper (D 7) (R 7) [6,40,96,320,130,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1816 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 267, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 100 328 146 160 80 129 257), lower := (rows 7 42 100 328 146 160 80 128 256), losses := [] }

theorem u1817 : Upper (D 7) (R 7) [6,40,96,320,130,128,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1817 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 392 145 33 66 208 336), lower := (rows 7 42 100 392 145 33 66 128 256), losses := [] }

theorem u1818 : Upper (D 7) (R 7) [6,40,96,384,129,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1818 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 472, targets := 32 },{ cop := 2, region := 394, targets := 1 }], pairs := [(1,0),(3,5),(4,5)], upper := (rows 7 42 100 392 145 33 80 194 322), lower := (rows 7 42 100 392 145 33 80 128 256), losses := [] }

theorem u1819 : Upper (D 7) (R 7) [6,40,96,384,129,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1819 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 410, targets := 1 },{ cop := 3, region := 103, targets := 128 }], pairs := [(0,7),(1,0),(3,0),(4,0)], upper := (rows 7 42 100 392 208 33 65 146 274), lower := (rows 7 42 100 392 208 33 65 128 256), losses := [] }

theorem u1820 : Upper (D 7) (R 7) [6,40,96,384,192,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1820 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 472, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 7 42 100 392 208 33 66 145 273), lower := (rows 7 42 100 392 208 33 66 128 256), losses := [] }

theorem u1821 : Upper (D 7) (R 7) [6,40,96,384,192,1,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1821 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 395, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 7 42 100 392 208 33 80 131 259), lower := (rows 7 42 100 392 208 33 80 128 256), losses := [] }

theorem u1822 : Upper (D 7) (R 7) [6,40,96,384,192,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1822 [(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5),(4,7)], upper := (rows 7 42 196 25 82 160 65 416 288), lower := (rows 7 42 196 25 82 160 65 128 256), losses := [] }

theorem u1823 : Upper (D 7) (R 7) [6,40,192,17,66,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1823 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 397, targets := 32 },{ cop := 1, region := 80, targets := 1 }], pairs := [(0,5),(2,5),(3,5),(4,0)], upper := (rows 7 42 196 25 82 160 96 385 257), lower := (rows 7 42 196 25 82 160 96 128 256), losses := [] }

theorem u1824 : Upper (D 7) (R 7) [6,40,192,17,66,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1824 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1825 : Route 9 := (fun mask => (mask,id))

def c1825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1825 : Upper (D 7) (R 7) [6,40,192,17,66,128,256] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,66,128,256] 13 (by decide) (choices 1) [1,32] r1825 c1825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u82
  · exact u83

def b1826 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 88, targets := 160 }], pairs := [(3,5),(3,7),(4,5)], upper := (rows 7 42 196 25 82 288 65 160 416), lower := (rows 7 42 196 25 82 288 65 128 256), losses := [] }

theorem u1826 : Upper (D 7) (R 7) [6,40,192,17,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1826 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 141, targets := 32 }], pairs := [(0,5),(2,5),(3,5)], upper := (rows 7 42 196 25 82 288 96 129 385), lower := (rows 7 42 196 25 82 288 96 128 256), losses := [] }

theorem u1827 : Upper (D 7) (R 7) [6,40,192,17,66,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1827 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 25 82 288 192 161 289), lower := (rows 7 42 196 25 82 288 192 128 256), losses := [] }

theorem u1828 : Upper (D 7) (R 7) [6,40,192,17,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1828 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 5, region := 132, targets := 3 }], pairs := [(2,0),(2,1),(4,0),(4,6)], upper := (rows 7 42 196 25 274 96 65 160 416), lower := (rows 7 42 196 25 274 96 65 128 256), losses := [] }

theorem u1829 : Upper (D 7) (R 7) [6,40,192,17,258,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1829 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 196 25 274 96 96 129 385), lower := (rows 7 42 196 25 274 96 96 128 256), losses := [] }

theorem u1830 : Upper (D 7) (R 7) [6,40,192,17,258,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1830 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 274 96 192 161 289), lower := (rows 7 42 196 25 274 96 192 128 256), losses := [] }

theorem u1831 : Upper (D 7) (R 7) [6,40,192,17,258,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1831 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 130, camps := [{ cop := 1, region := 400, targets := 65 },{ cop := 1, region := 197, targets := 32 }], pairs := [(0,5),(2,5),(4,0),(4,6)], upper := (rows 7 42 196 25 304 96 65 130 386), lower := (rows 7 42 196 25 304 96 65 128 256), losses := [] }

theorem u1832 : Upper (D 7) (R 7) [6,40,192,17,288,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1832 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 129, camps := [{ cop := 1, region := 197, targets := 32 },{ cop := 3, region := 98, targets := 129 }], pairs := [(0,5),(1,0),(1,7),(2,5)], upper := (rows 7 42 196 25 304 96 66 129 385), lower := (rows 7 42 196 25 304 96 66 128 256), losses := [] }

theorem u1833 : Upper (D 7) (R 7) [6,40,192,17,288,64,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1833 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 304 96 192 131 259), lower := (rows 7 42 196 25 304 96 192 128 256), losses := [] }

theorem u1834 : Upper (D 7) (R 7) [6,40,192,17,288,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1834 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 160, camps := [{ cop := 3, region := 34, targets := 65 },{ cop := 3, region := 34, targets := 128 }], pairs := [(1,0),(1,6),(1,7),(2,0)], upper := (rows 7 42 196 25 336 34 65 160 416), lower := (rows 7 42 196 25 336 34 65 128 256), losses := [{ target := 0, region := (rows 0 10 84 8 84 43 64 235 363), good := (rows 438 426 468 446 468 418 500 128 256) }] }

theorem u1835 : Upper (D 7) (R 7) [6,40,192,17,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1835 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 34, targets := 129 },{ cop := 3, region := 34, targets := 64 }], pairs := [(1,0),(1,6),(1,7),(2,1)], upper := (rows 7 42 196 25 336 34 96 129 385), lower := (rows 7 42 196 25 336 34 96 128 256), losses := [{ target := 1, region := (rows 1 0 7 9 19 32 98 137 265), good := (rows 477 508 196 413 336 116 96 128 256) }] }

theorem u1836 : Upper (D 7) (R 7) [6,40,192,17,320,2,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1836 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 25 336 34 192 161 289), lower := (rows 7 42 196 25 336 34 192 128 256), losses := [] }

theorem u1837 : Upper (D 7) (R 7) [6,40,192,17,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1837 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 162, targets := 65 }], pairs := [(1,0),(1,6),(2,0),(4,0)], upper := (rows 7 42 196 25 336 160 65 162 290), lower := (rows 7 42 196 25 336 160 65 128 256), losses := [{ target := 0, region := (rows 0 10 68 8 80 239 64 139 267), good := (rows 422 426 244 442 372 160 500 160 256) }] }

theorem u1838 : Upper (D 7) (R 7) [6,40,192,17,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1838 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def r1839 : Route 9 := (fun mask => (mask,id))

def c1839 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1839 : Upper (D 7) (R 7) [6,40,192,17,320,128,2] 13 := by
  apply FastRouting.sound _ _ [6,40,192,17,320,128,2] 13 (by decide) (choices 1) [1,32] r1839 c1839
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u84
  · exact u85

def b1840 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 68, targets := 3 },{ cop := 3, region := 162, targets := 64 }], pairs := [(1,6),(2,0),(2,1),(3,7)], upper := (rows 7 42 196 25 336 160 96 131 259), lower := (rows 7 42 196 25 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 17 32 98 0 257), good := (rows 351 106 68 281 336 96 96 0 256) }] }

theorem u1840 : Upper (D 7) (R 7) [6,40,192,17,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1840 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 4, region := 106, targets := 128 }], pairs := [(1,7),(2,1),(3,7),(4,1)], upper := (rows 7 42 196 26 273 96 65 160 416), lower := (rows 7 42 196 26 273 96 65 128 256), losses := [] }

theorem u1841 : Upper (D 7) (R 7) [6,40,192,18,257,64,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1841 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 7 42 196 26 273 96 96 129 385), lower := (rows 7 42 196 26 273 96 96 128 256), losses := [] }

theorem u1842 : Upper (D 7) (R 7) [6,40,192,18,257,64,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1842 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 26 273 96 192 161 289), lower := (rows 7 42 196 26 273 96 192 128 256), losses := [] }

theorem u1843 : Upper (D 7) (R 7) [6,40,192,18,257,64,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1843 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 160, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 196 26 336 33 65 160 416), lower := (rows 7 42 196 26 336 33 65 128 256), losses := [{ target := 6, region := (rows 1 18 4 24 16 97 0 247 375), good := (rows 423 426 420 410 442 417 417 128 256) }] }

theorem u1844 : Upper (D 7) (R 7) [6,40,192,18,320,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1844 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(2,1),(2,5),(4,1),(4,5)], upper := (rows 7 42 196 26 336 33 96 129 385), lower := (rows 7 42 196 26 336 33 96 128 256), losses := [{ target := 5, region := (rows 1 2 68 8 80 0 64 161 289), good := (rows 391 394 212 26 340 385 468 128 256) }] }

theorem u1845 : Upper (D 7) (R 7) [6,40,192,18,320,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1845 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7),(4,7)], upper := (rows 7 42 196 26 336 33 192 161 289), lower := (rows 7 42 196 26 336 33 192 128 256), losses := [] }

theorem u1846 : Upper (D 7) (R 7) [6,40,192,18,320,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1846 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 500, targets := 2 }], pairs := [(1,6),(2,1),(3,6),(4,1)], upper := (rows 7 42 196 26 336 160 65 161 289), lower := (rows 7 42 196 26 336 160 65 128 256), losses := [{ target := 6, region := (rows 1 26 4 24 16 245 0 193 321), good := (rows 423 42 420 58 442 160 417 160 256) }] }

theorem u1847 : Upper (D 7) (R 7) [6,40,192,18,320,128,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1847 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 500, targets := 2 },{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0),(2,1),(3,7),(4,1)], upper := (rows 7 42 196 26 336 160 96 129 257), lower := (rows 7 42 196 26 336 160 96 128 256), losses := [{ target := 7, region := (rows 1 2 4 9 17 32 98 0 257), good := (rows 351 106 68 90 336 96 96 0 256) }] }

theorem u1848 : Upper (D 7) (R 7) [6,40,192,18,320,128,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1848 []
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 196 73 49 288 66 144 400), lower := (rows 7 42 196 73 49 288 66 128 256), losses := [] }

theorem u1849 : Upper (D 7) (R 7) [6,40,192,65,33,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1849 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(2,0)], upper := (rows 7 42 196 73 49 288 80 130 386), lower := (rows 7 42 196 73 49 288 80 128 256), losses := [] }

theorem u1850 : Upper (D 7) (R 7) [6,40,192,65,33,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1850 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7),(1,7),(3,7)], upper := (rows 7 42 196 73 49 288 192 146 274), lower := (rows 7 42 196 73 49 288 192 128 256), losses := [] }

theorem u1851 : Upper (D 7) (R 7) [6,40,192,65,33,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1851 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 288, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 146 48 65 416 288), lower := (rows 7 42 196 73 146 48 65 128 256), losses := [] }

theorem u1852 : Upper (D 7) (R 7) [6,40,192,65,130,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1852 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 388, targets := 34 },{ cop := 3, region := 434, targets := 64 }], pairs := [(1,6),(2,1),(2,5)], upper := (rows 7 42 196 73 146 48 96 385 257), lower := (rows 7 42 196 73 146 48 96 128 256), losses := [] }

theorem u1853 : Upper (D 7) (R 7) [6,40,192,65,130,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1853 [(5,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 178, targets := 64 }], pairs := [(1,6),(4,6)], upper := (rows 7 42 196 73 146 48 320 161 289), lower := (rows 7 42 196 73 146 48 320 128 256), losses := [] }

theorem u1854 : Upper (D 7) (R 7) [6,40,192,65,130,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1854 [(5,4),(6,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 146 288 65 176 304), lower := (rows 7 42 196 73 146 288 65 128 256), losses := [] }

theorem u1855 : Upper (D 7) (R 7) [6,40,192,65,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1855 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 299, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 42 196 73 146 288 80 161 289), lower := (rows 7 42 196 73 146 288 80 128 256), losses := [] }

theorem u1856 : Upper (D 7) (R 7) [6,40,192,65,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1856 [(5,8),(6,4)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 434, targets := 64 },{ cop := 0, region := 144, targets := 32 }], pairs := [(1,6),(4,5),(4,6)], upper := (rows 7 42 196 73 146 288 96 145 273), lower := (rows 7 42 196 73 146 288 96 128 256), losses := [] }

theorem u1857 : Upper (D 7) (R 7) [6,40,192,65,130,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1857 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 72, targets := 162 }], pairs := [(3,1),(3,5),(3,7)], upper := (rows 7 42 196 73 176 288 65 146 274), lower := (rows 7 42 196 73 176 288 65 128 256), losses := [] }

theorem u1858 : Upper (D 7) (R 7) [6,40,192,65,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1858 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 432, targets := 66 },{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5),(4,1),(4,6)], upper := (rows 7 42 196 73 176 288 66 145 273), lower := (rows 7 42 196 73 176 288 66 128 256), losses := [] }

theorem u1859 : Upper (D 7) (R 7) [6,40,192,65,160,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 7) 14 b1859 [(5,8)]
    (constants 7).1 (constants 7).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P07
