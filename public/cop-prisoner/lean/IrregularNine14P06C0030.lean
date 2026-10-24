import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0001

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 261, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 162 324 44 82 33 72 145 273), lower := (rows 7 162 324 44 82 33 72 128 256), losses := [] }

theorem u1800 : Upper (D 6) (R 6) [6,160,320,36,66,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1800
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 80, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 162 324 44 82 33 80 137 265), lower := (rows 7 162 324 44 82 33 80 128 256), losses := [] }

theorem u1801 : Upper (D 6) (R 6) [6,160,320,36,66,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1801
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 120, targets := 2 },{ cop := 0, region := 40, targets := 64 }], pairs := [(3,1),(3,6),(4,1)], upper := (rows 7 162 324 44 88 33 65 146 274), lower := (rows 7 162 324 44 88 33 65 128 256), losses := [] }

theorem u1802 : Upper (D 6) (R 6) [6,160,320,36,72,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1802
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1803 : Route 9 := (fun mask => (mask,id))

def c1803 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1803 : Upper (D 6) (R 6) [6,160,320,36,72,1,2] 13 := by
  apply FastRouting.sound _ _ [6,160,320,36,72,1,2] 13 (by decide) (choices 1) [1,16] r1803 c1803
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u98
  · exact u99

def b1804 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 162 324 44 88 33 80 131 259), lower := (rows 7 162 324 44 88 33 80 128 256), losses := [] }

theorem u1804 : Upper (D 6) (R 6) [6,160,320,36,72,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1804
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 420, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 37 76 112 160 66 388 260), lower := (rows 11 19 37 76 112 160 66 128 256), losses := [] }

theorem u1805 : Upper (D 6) (R 6) [10,17,33,68,96,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1805
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 258, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 19 37 76 112 160 68 386 258), lower := (rows 11 19 37 76 112 160 68 128 256), losses := [] }

theorem u1806 : Upper (D 6) (R 6) [10,17,33,68,96,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1806
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 164, targets := 64 }], pairs := [(2,6)], upper := (rows 11 19 37 76 112 160 320 134 262), lower := (rows 11 19 37 76 112 160 320 128 256), losses := [] }

theorem u1807 : Upper (D 6) (R 6) [10,17,33,68,96,128,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1807
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 432, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 19 37 76 176 288 66 196 324), lower := (rows 11 19 37 76 176 288 66 128 256), losses := [] }

theorem u1808 : Upper (D 6) (R 6) [10,17,33,68,160,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1808
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 19 37 76 176 288 68 194 322), lower := (rows 11 19 37 76 176 288 68 128 256), losses := [] }

theorem u1809 : Upper (D 6) (R 6) [10,17,33,68,160,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1809
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1810 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 37 76 208 288 66 164 292), lower := (rows 11 19 37 76 208 288 66 128 256), losses := [] }

theorem u1810 : Upper (D 6) (R 6) [10,17,33,68,192,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1810
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 19 37 76 208 288 68 162 290), lower := (rows 11 19 37 76 208 288 68 128 256), losses := [] }

theorem u1811 : Upper (D 6) (R 6) [10,17,33,68,192,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1811
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 147, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 19 37 76 208 288 96 134 262), lower := (rows 11 19 37 76 208 288 96 128 256), losses := [] }

theorem u1812 : Upper (D 6) (R 6) [10,17,33,68,192,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1812
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 82, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 11 19 37 140 112 288 66 196 324), lower := (rows 11 19 37 140 112 288 66 128 256), losses := [] }

theorem u1813 : Upper (D 6) (R 6) [10,17,33,132,96,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1813
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 19 37 140 112 288 68 194 322), lower := (rows 11 19 37 140 112 288 68 128 256), losses := [] }

theorem u1814 : Upper (D 6) (R 6) [10,17,33,132,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1814
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 37 140 276 96 66 224 352), lower := (rows 11 19 37 140 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 28 103 67 231 359), good := (rows 506 506 508 444 444 480 482 128 256) },{ target := 1, region := (rows 1 0 4 12 20 96 64 224 352), good := (rows 9 17 445 156 284 480 480 128 256) }] }

theorem u1815 : Upper (D 6) (R 6) [10,17,33,132,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1815
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 37 140 276 96 96 194 322), lower := (rows 11 19 37 140 276 96 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 511 511 131 259), good := (rows 490 498 508 252 380 96 96 224 352) }] }

theorem u1816 : Upper (D 6) (R 6) [10,17,33,132,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1816
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 68, camps := [], pairs := [(3,0),(3,5),(4,0)], upper := (rows 11 19 37 140 304 96 66 196 324), lower := (rows 11 19 37 140 304 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 103 67 132 260), good := (rows 122 114 508 444 304 96 98 128 256) },{ target := 5, region := (rows 1 2 4 12 16 0 67 132 260), good := (rows 75 83 461 396 272 64 66 128 256) }] }

theorem u1817 : Upper (D 6) (R 6) [10,17,33,132,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1817
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 37 140 304 96 68 194 322), lower := (rows 11 19 37 140 304 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 23 109 76 129 257), good := (rows 506 434 508 252 304 96 124 128 256) }] }

theorem u1818 : Upper (D 6) (R 6) [10,17,33,132,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1818
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 136, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 37 140 336 96 66 164 292), lower := (rows 11 19 37 140 336 96 66 128 256), losses := [] }

theorem u1819 : Upper (D 6) (R 6) [10,17,33,132,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1819
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 100, targets := 2 }], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 37 140 336 96 68 162 290), lower := (rows 11 19 37 140 336 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 21 125 76 131 259), good := (rows 506 434 508 252 368 96 124 128 256) }] }

theorem u1820 : Upper (D 6) (R 6) [10,17,33,132,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1820
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 19 37 140 336 96 96 134 262), lower := (rows 11 19 37 140 336 96 96 128 256), losses := [] }

theorem u1821 : Upper (D 6) (R 6) [10,17,33,132,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1821
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 19 37 168 276 96 66 196 324), lower := (rows 11 19 37 168 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 103 67 132 260), good := (rows 106 122 508 168 444 96 98 128 256) }] }

theorem u1822 : Upper (D 6) (R 6) [10,17,33,160,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1822
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 338, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 19 37 168 276 96 68 194 322), lower := (rows 11 19 37 168 276 96 68 128 256), losses := [] }

theorem u1823 : Upper (D 6) (R 6) [10,17,33,160,260,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1823
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 37 200 84 288 66 164 292), lower := (rows 11 19 37 200 84 288 66 128 256), losses := [] }

theorem u1824 : Upper (D 6) (R 6) [10,17,33,192,68,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1824
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 19 37 200 84 288 68 162 290), lower := (rows 11 19 37 200 84 288 68 128 256), losses := [] }

theorem u1825 : Upper (D 6) (R 6) [10,17,33,192,68,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1825
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 139, targets := 32 }], pairs := [(0,5),(1,5)], upper := (rows 11 19 37 200 84 288 96 134 262), lower := (rows 11 19 37 200 84 288 96 128 256), losses := [] }

theorem u1826 : Upper (D 6) (R 6) [10,17,33,192,68,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1826
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 260, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 82, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 200 112 36 66 388 260), lower := (rows 11 19 37 200 112 36 66 128 256), losses := [] }

theorem u1827 : Upper (D 6) (R 6) [10,17,33,192,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1827
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 258, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 200 112 36 68 386 258), lower := (rows 11 19 37 200 112 36 68 128 256), losses := [] }

theorem u1828 : Upper (D 6) (R 6) [10,17,33,192,96,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1828
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 37 200 112 36 320 134 262), lower := (rows 11 19 37 200 112 36 320 128 256), losses := [] }

theorem u1829 : Upper (D 6) (R 6) [10,17,33,192,96,4,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1829
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 4, camps := [{ cop := 0, region := 292, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 37 200 112 288 66 132 260), lower := (rows 11 19 37 200 112 288 66 128 256), losses := [] }

theorem u1830 : Upper (D 6) (R 6) [10,17,33,192,96,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1830
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 19 37 200 112 288 68 134 262), lower := (rows 11 19 37 200 112 288 68 128 256), losses := [] }

theorem u1831 : Upper (D 6) (R 6) [10,17,33,192,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1831
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 19 37 200 304 36 66 196 324), lower := (rows 11 19 37 200 304 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 52 36 67 132 260), good := (rows 74 82 508 200 304 444 66 128 256) }] }

theorem u1832 : Upper (D 6) (R 6) [10,17,33,192,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1832
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,5),(2,1),(2,6)], upper := (rows 11 19 37 200 304 36 68 194 322), lower := (rows 11 19 37 200 304 36 68 128 256), losses := [{ target := 5, region := (rows 19 18 4 24 16 0 100 144 272), good := (rows 11 411 69 200 475 68 68 128 256) }] }

theorem u1833 : Upper (D 6) (R 6) [10,17,33,192,288,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1833
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 19 37 200 336 36 66 164 292), lower := (rows 11 19 37 200 336 36 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 20 36 67 164 292), good := (rows 74 82 508 200 336 444 66 128 256) }] }

theorem u1834 : Upper (D 6) (R 6) [10,17,33,192,320,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1834
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1835 : Route 9 := (fun mask => (mask,id))

def c1835 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1835 : Upper (D 6) (R 6) [10,17,33,192,320,4,4] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,320,4,4] 13 (by decide) (choices 1) [2,32] r1835 c1835
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u100
  · exact u101

def r1836 : Route 9 := (fun mask => (mask,id))

def c1836 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1836 : Upper (D 6) (R 6) [10,17,33,192,320,4,32] 13 := by
  apply FastRouting.sound _ _ [10,17,33,192,320,4,32] 13 (by decide) (choices 1) [2,4] r1836 c1836
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u102
  · exact u103

def b1837 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 392, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 19 37 392 84 96 66 164 292), lower := (rows 11 19 37 392 84 96 66 128 256), losses := [] }

theorem u1837 : Upper (D 6) (R 6) [10,17,33,384,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1837
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 427, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 37 392 84 96 68 162 290), lower := (rows 11 19 37 392 84 96 68 128 256), losses := [] }

theorem u1838 : Upper (D 6) (R 6) [10,17,33,384,68,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1838
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 395, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 37 392 84 96 96 134 262), lower := (rows 11 19 37 392 84 96 96 128 256), losses := [] }

theorem u1839 : Upper (D 6) (R 6) [10,17,33,384,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1839
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 66 },{ cop := 2, region := 82, targets := 4 }], pairs := [(1,2),(2,1),(2,6)], upper := (rows 11 19 37 392 112 36 66 196 324), lower := (rows 11 19 37 392 112 36 66 128 256), losses := [] }

theorem u1840 : Upper (D 6) (R 6) [10,17,33,384,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1840
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 395, targets := 36 }], pairs := [(0,2),(0,5),(1,2)], upper := (rows 11 19 37 392 112 36 68 194 322), lower := (rows 11 19 37 392 112 36 68 128 256), losses := [] }

theorem u1841 : Upper (D 6) (R 6) [10,17,33,384,96,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1841
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 100 140 276 33 66 224 352), lower := (rows 11 19 100 140 276 33 66 128 256), losses := [] }

theorem u1842 : Upper (D 6) (R 6) [10,17,96,132,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1842
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 411, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 100 140 276 33 96 194 322), lower := (rows 11 19 100 140 276 33 96 128 256), losses := [] }

theorem u1843 : Upper (D 6) (R 6) [10,17,96,132,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1843
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 100 140 304 33 66 196 324), lower := (rows 11 19 100 140 304 33 66 128 256), losses := [] }

theorem u1844 : Upper (D 6) (R 6) [10,17,96,132,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1844
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 100 140 304 33 68 194 322), lower := (rows 11 19 100 140 304 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 52 42 48 32 126 131 259), good := (rows 458 478 124 204 380 508 68 128 256) }] }

theorem u1845 : Upper (D 6) (R 6) [10,17,96,132,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1845
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 100 140 304 34 65 196 324), lower := (rows 11 19 100 140 304 34 65 128 256), losses := [] }

theorem u1846 : Upper (D 6) (R 6) [10,17,96,132,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1846
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,1)], upper := (rows 11 19 100 140 304 34 68 193 321), lower := (rows 11 19 100 140 304 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 52 42 48 32 126 131 259), good := (rows 457 477 124 204 380 508 68 128 256) }] }

theorem u1847 : Upper (D 6) (R 6) [10,17,96,132,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1847
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1848 : Route 9 := (fun mask => (mask,id))

def c1848 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1848 : Upper (D 6) (R 6) [10,17,96,132,288,4,1] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288,4,1] 13 (by decide) (choices 1) [2,64] r1848 c1848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u104
  · exact u105

def r1849 : Route 9 := (fun mask => (mask,id))

def c1849 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1849 : Upper (D 6) (R 6) [10,17,96,132,288,4,2] 13 := by
  apply FastRouting.sound _ _ [10,17,96,132,288,4,2] 13 (by decide) (choices 1) [1,64] r1849 c1849
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u106
  · exact u107

def b1850 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 100 168 336 33 66 132 260), lower := (rows 11 19 100 168 336 33 66 128 256), losses := [] }

theorem u1850 : Upper (D 6) (R 6) [10,17,96,160,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1850
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 100 168 336 33 68 134 262), lower := (rows 11 19 100 168 336 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 44 40 51 32 109 129 257), good := (rows 478 466 124 252 336 508 68 128 256) }] }

theorem u1851 : Upper (D 6) (R 6) [10,17,96,160,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1851
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 4, camps := [{ cop := 2, region := 408, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 100 168 336 34 65 132 260), lower := (rows 11 19 100 168 336 34 65 128 256), losses := [] }

theorem u1852 : Upper (D 6) (R 6) [10,17,96,160,320,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1852
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 68, targets := 3 }], pairs := [(2,0),(2,1),(4,1)], upper := (rows 11 19 100 168 336 34 68 133 261), lower := (rows 11 19 100 168 336 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 44 8 19 32 109 129 257), good := (rows 477 465 100 236 336 116 68 128 256) }] }

theorem u1853 : Upper (D 6) (R 6) [10,17,96,160,320,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1853
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 411, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 100 168 336 36 68 131 259), lower := (rows 11 19 100 168 336 36 68 128 256), losses := [] }

theorem u1854 : Upper (D 6) (R 6) [10,17,96,160,320,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1854
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 19 133 44 112 288 66 196 324), lower := (rows 11 19 133 44 112 288 66 128 256), losses := [] }

theorem u1855 : Upper (D 6) (R 6) [10,17,129,36,96,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1855
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 80, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 11 19 133 44 112 288 68 194 322), lower := (rows 11 19 133 44 112 288 68 128 256), losses := [] }

theorem u1856 : Upper (D 6) (R 6) [10,17,129,36,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1856
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 19 133 44 276 96 66 224 352), lower := (rows 11 19 133 44 276 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 28 103 67 231 359), good := (rows 506 506 508 444 444 480 482 128 256) },{ target := 1, region := (rows 1 0 4 8 24 96 64 224 352), good := (rows 25 17 133 444 276 480 480 128 256) }] }

theorem u1857 : Upper (D 6) (R 6) [10,17,129,36,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1857
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 133 44 276 96 96 194 322), lower := (rows 11 19 133 44 276 96 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 511 511 131 259), good := (rows 490 506 508 124 380 96 96 224 352) }] }

theorem u1858 : Upper (D 6) (R 6) [10,17,129,36,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1858
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 19 133 44 304 96 66 196 324), lower := (rows 11 19 133 44 304 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 103 67 132 260), good := (rows 122 114 508 444 304 96 98 128 256) }] }

theorem u1859 : Upper (D 6) (R 6) [10,17,129,36,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1859
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P06
