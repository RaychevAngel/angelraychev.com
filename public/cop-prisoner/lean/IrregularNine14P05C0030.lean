import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P05C0001
import IrregularNine14P05C0002

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 38, camps := [{ cop := 1, region := 48, targets := 2 },{ cop := 1, region := 48, targets := 4 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 84 392 56 33 102 166 294), lower := (rows 7 11 84 392 56 33 64 128 256), losses := [] }

theorem u1800 : Upper (D 5) (R 5) [6,9,80,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1800
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 37, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 84 392 56 34 101 165 293), lower := (rows 7 11 84 392 56 34 64 128 256), losses := [] }

theorem u1801 : Upper (D 5) (R 5) [6,9,80,384,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1801
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 35, camps := [], pairs := [(4,0),(4,1)], upper := (rows 7 11 84 392 56 36 99 163 291), lower := (rows 7 11 84 392 56 36 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 18 37 64 128 256), good := (rows 54 58 116 392 56 36 64 128 256) },{ target := 1, region := (rows 1 0 4 8 18 37 64 128 256), good := (rows 53 57 116 392 56 36 64 128 256) }] }

theorem u1802 : Upper (D 5) (R 5) [6,9,80,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1802
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 28, camps := [], pairs := [(2,0),(3,0)], upper := (rows 7 11 100 168 273 34 92 156 284), lower := (rows 7 11 100 168 273 34 64 128 256), losses := [{ target := 0, region := (rows 0 2 20 24 16 35 80 144 272), good := (rows 38 42 100 168 508 34 64 128 256) }] }

theorem u1803 : Upper (D 5) (R 5) [6,9,96,160,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1803
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 26, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 168 273 36 90 154 282), lower := (rows 7 11 100 168 273 36 64 128 256), losses := [] }

theorem u1804 : Upper (D 5) (R 5) [6,9,96,160,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1804
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 100 168 273 40 86 150 278), lower := (rows 7 11 100 168 273 40 64 128 256), losses := [] }

theorem u1805 : Upper (D 5) (R 5) [6,9,96,160,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1805
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1806 : Route 9 := (fun mask => (mask,id))

def c1806 : Nat → Fin 9 := (fun mask => match mask with | 16 => 4 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1806 : Upper (D 5) (R 5) [6,9,96,160,257,16] 13 := by
  apply FastRouting.sound _ _ [6,9,96,160,257,16] 13 (by decide) (choices 1) [2,4,8] r1806 c1806
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u115
  · exact u116
  · exact u117

def b1807 : PairBound 9 := { available := 26, camps := [], pairs := [(4,0),(4,5)], upper := (rows 7 11 100 168 276 33 90 154 282), lower := (rows 7 11 100 168 276 33 64 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 17 32 66 130 258), good := (rows 470 474 100 168 276 48 64 128 256) },{ target := 5, region := (rows 1 2 4 8 17 0 66 130 258), good := (rows 471 475 68 136 276 17 64 128 256) }] }

theorem u1807 : Upper (D 5) (R 5) [6,9,96,160,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1807
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 25, camps := [], pairs := [(2,1),(3,1)], upper := (rows 7 11 100 168 276 34 89 153 281), lower := (rows 7 11 100 168 276 34 64 128 256), losses := [{ target := 1, region := (rows 1 0 36 40 49 32 66 130 258), good := (rows 469 473 124 188 276 508 64 128 256) }] }

theorem u1808 : Upper (D 5) (R 5) [6,9,96,160,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1808
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 19, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 11 100 168 276 40 83 147 275), lower := (rows 7 11 100 168 276 40 64 128 256), losses := [] }

theorem u1809 : Upper (D 5) (R 5) [6,9,96,160,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1809
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1810 : PairBound 9 := { available := 11, camps := [], pairs := [(4,5)], upper := (rows 7 11 100 168 276 48 75 139 267), lower := (rows 7 11 100 168 276 48 64 128 256), losses := [{ target := 5, region := (rows 1 2 4 8 17 0 66 130 258), good := (rows 471 475 68 136 276 16 64 128 256) }] }

theorem u1810 : Upper (D 5) (R 5) [6,9,96,160,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1810
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 392 49 34 92 156 284), lower := (rows 7 11 100 392 49 34 64 128 256), losses := [] }

theorem u1811 : Upper (D 5) (R 5) [6,9,96,384,33,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1811
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 26, camps := [{ cop := 4, region := 394, targets := 36 }], pairs := [(1,2),(1,5)], upper := (rows 7 11 100 392 49 36 90 154 282), lower := (rows 7 11 100 392 49 36 64 128 256), losses := [] }

theorem u1812 : Upper (D 5) (R 5) [6,9,96,384,33,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1812
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 48, targets := 2 },{ cop := 1, region := 48, targets := 4 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 100 392 49 40 86 150 278), lower := (rows 7 11 100 392 49 40 64 128 256), losses := [] }

theorem u1813 : Upper (D 5) (R 5) [6,9,96,384,33,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1813
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 48, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 100 392 49 48 78 142 270), lower := (rows 7 11 100 392 49 48 64 128 256), losses := [] }

theorem u1814 : Upper (D 5) (R 5) [6,9,96,384,33,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1814
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 28, camps := [{ cop := 4, region := 460, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 392 50 33 92 156 284), lower := (rows 7 11 100 392 50 33 64 128 256), losses := [] }

theorem u1815 : Upper (D 5) (R 5) [6,9,96,384,34,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1815
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 25, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 392 50 36 89 153 281), lower := (rows 7 11 100 392 50 36 64 128 256), losses := [] }

theorem u1816 : Upper (D 5) (R 5) [6,9,96,384,34,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1816
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 100 392 50 40 85 149 277), lower := (rows 7 11 100 392 50 40 64 128 256), losses := [] }

theorem u1817 : Upper (D 5) (R 5) [6,9,96,384,34,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1817
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 13, camps := [{ cop := 1, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 7 11 100 392 50 48 77 141 269), lower := (rows 7 11 100 392 50 48 64 128 256), losses := [] }

theorem u1818 : Upper (D 5) (R 5) [6,9,96,384,34,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1818
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 48, targets := 2 },{ cop := 1, region := 48, targets := 4 }], pairs := [(4,1),(4,2)], upper := (rows 7 11 100 392 56 33 86 150 278), lower := (rows 7 11 100 392 56 33 64 128 256), losses := [] }

theorem u1819 : Upper (D 5) (R 5) [6,9,96,384,40,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1819
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 21, camps := [{ cop := 1, region := 48, targets := 5 }], pairs := [(4,0),(4,2)], upper := (rows 7 11 100 392 56 34 85 149 277), lower := (rows 7 11 100 392 56 34 64 128 256), losses := [] }

theorem u1820 : Upper (D 5) (R 5) [6,9,96,384,40,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1820
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 19, camps := [{ cop := 6, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 11 100 392 56 36 83 147 275), lower := (rows 7 11 100 392 56 36 64 128 256), losses := [] }

theorem u1821 : Upper (D 5) (R 5) [6,9,96,384,40,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1821
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 395, targets := 32 }], pairs := [(0,5)], upper := (rows 7 11 100 392 56 48 71 135 263), lower := (rows 7 11 100 392 56 48 64 128 256), losses := [] }

theorem u1822 : Upper (D 5) (R 5) [6,9,96,384,40,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1822
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 73 176 34 332 396 268), lower := (rows 7 19 44 73 176 34 64 128 256), losses := [] }

theorem u1823 : Upper (D 5) (R 5) [6,17,40,65,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1823
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 19 44 73 176 36 330 394 266), lower := (rows 7 19 44 73 176 36 64 128 256), losses := [] }

theorem u1824 : Upper (D 5) (R 5) [6,17,40,65,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1824
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 262, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 73 176 40 326 390 262), lower := (rows 7 19 44 73 176 40 64 128 256), losses := [] }

theorem u1825 : Upper (D 5) (R 5) [6,17,40,65,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1825
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 44 73 176 288 78 142 270), lower := (rows 7 19 44 73 176 288 64 128 256), losses := [] }

theorem u1826 : Upper (D 5) (R 5) [6,17,40,65,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1826
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 73 400 34 108 172 300), lower := (rows 7 19 44 73 400 34 64 128 256), losses := [] }

theorem u1827 : Upper (D 5) (R 5) [6,17,40,65,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1827
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 42, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 73 400 36 106 170 298), lower := (rows 7 19 44 73 400 36 64 128 256), losses := [] }

theorem u1828 : Upper (D 5) (R 5) [6,17,40,65,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1828
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 38, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 73 400 40 102 166 294), lower := (rows 7 19 44 73 400 40 64 128 256), losses := [] }

theorem u1829 : Upper (D 5) (R 5) [6,17,40,65,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1829
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 292, camps := [{ cop := 2, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 74 152 33 356 420 292), lower := (rows 7 19 44 74 152 33 64 128 256), losses := [] }

theorem u1830 : Upper (D 5) (R 5) [6,17,40,66,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1830
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 289, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 74 152 36 353 417 289), lower := (rows 7 19 44 74 152 36 64 128 256), losses := [] }

theorem u1831 : Upper (D 5) (R 5) [6,17,40,66,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1831
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 37, camps := [], pairs := [(2,1)], upper := (rows 7 19 44 74 152 288 101 165 293), lower := (rows 7 19 44 74 152 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 28 8 24 299 67 131 259), good := (rows 485 501 60 508 188 288 64 128 288) }] }

theorem u1832 : Upper (D 5) (R 5) [6,17,40,66,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1832
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 268, camps := [{ cop := 2, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 74 176 33 332 396 268), lower := (rows 7 19 44 74 176 33 64 128 256), losses := [] }

theorem u1833 : Upper (D 5) (R 5) [6,17,40,66,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1833
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 19 44 74 176 36 329 393 265), lower := (rows 7 19 44 74 176 36 64 128 256), losses := [] }

theorem u1834 : Upper (D 5) (R 5) [6,17,40,66,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1834
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 261, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 74 176 40 325 389 261), lower := (rows 7 19 44 74 176 40 64 128 256), losses := [] }

theorem u1835 : Upper (D 5) (R 5) [6,17,40,66,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1835
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 44 74 176 288 77 141 269), lower := (rows 7 19 44 74 176 288 64 128 256), losses := [] }

theorem u1836 : Upper (D 5) (R 5) [6,17,40,66,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1836
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 44, camps := [{ cop := 2, region := 400, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 19 44 74 400 33 108 172 300), lower := (rows 7 19 44 74 400 33 64 128 256), losses := [] }

theorem u1837 : Upper (D 5) (R 5) [6,17,40,66,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1837
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 41, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 74 400 36 105 169 297), lower := (rows 7 19 44 74 400 36 64 128 256), losses := [] }

theorem u1838 : Upper (D 5) (R 5) [6,17,40,66,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1838
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 37, camps := [{ cop := 2, region := 403, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 74 400 40 101 165 293), lower := (rows 7 19 44 74 400 40 64 128 256), losses := [] }

theorem u1839 : Upper (D 5) (R 5) [6,17,40,66,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1839
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 290, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 19 44 76 152 33 354 418 290), lower := (rows 7 19 44 76 152 33 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 20 35 99 163 291), good := (rows 499 499 504 88 152 483 64 128 256) }] }

theorem u1840 : Upper (D 5) (R 5) [6,17,40,68,136,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1840
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1841 : Route 9 := (fun mask => (mask,id))

def c1841 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | _ => 0)

theorem u1841 : Upper (D 5) (R 5) [6,17,40,68,136,2] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,136,2] 13 (by decide) (choices 1) [1,32,256] r1841 c1841
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u118
  · exact u119
  · exact u120

def r1842 : Route 9 := (fun mask => (mask,id))

def c1842 : Nat → Fin 9 := (fun mask => match mask with | 4 => 2 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1842 : Upper (D 5) (R 5) [6,17,40,68,136,256] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,136,256] 13 (by decide) (choices 1) [1,2,32] r1842 c1842
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u121
  · exact u122
  · exact u123

def b1843 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 328, targets := 1 },{ cop := 0, region := 328, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 44 76 176 33 330 394 266), lower := (rows 7 19 44 76 176 33 64 128 256), losses := [] }

theorem u1843 : Upper (D 5) (R 5) [6,17,40,68,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1843
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 265, camps := [{ cop := 0, region := 328, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 76 176 34 329 393 265), lower := (rows 7 19 44 76 176 34 64 128 256), losses := [] }

theorem u1844 : Upper (D 5) (R 5) [6,17,40,68,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1844
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 259, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 76 176 40 323 387 259), lower := (rows 7 19 44 76 176 40 64 128 256), losses := [] }

theorem u1845 : Upper (D 5) (R 5) [6,17,40,68,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1845
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 7 19 44 76 176 288 75 139 267), lower := (rows 7 19 44 76 176 288 64 128 256), losses := [] }

theorem u1846 : Upper (D 5) (R 5) [6,17,40,68,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1846
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 42, camps := [], pairs := [(1,2),(4,2)], upper := (rows 7 19 44 76 400 33 106 170 298), lower := (rows 7 19 44 76 400 33 64 128 256), losses := [{ target := 2, region := (rows 1 35 0 8 29 35 68 132 260), good := (rows 499 51 506 472 400 51 64 128 256) }] }

theorem u1847 : Upper (D 5) (R 5) [6,17,40,68,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1847
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1848 : Route 9 := (fun mask => (mask,id))

def c1848 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1848 : Upper (D 5) (R 5) [6,17,40,68,384,2] 13 := by
  apply FastRouting.sound _ _ [6,17,40,68,384,2] 13 (by decide) (choices 1) [1,8,32] r1848 c1848
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u124
  · exact u125
  · exact u126

def b1849 : PairBound 9 := { available := 35, camps := [{ cop := 6, region := 44, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 76 400 40 99 163 291), lower := (rows 7 19 44 76 400 40 64 128 256), losses := [] }

theorem u1849 : Upper (D 5) (R 5) [6,17,40,68,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1849
    (constants 5).1 (constants 5).2 (by decide +kernel)

def r1850 : Route 9 := (fun mask => (mask,id))

def c1850 : Nat → Fin 9 := (fun mask => match mask with | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1850 : Upper (D 5) (R 5) [6,17,40,192,264,1] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192,264,1] 13 (by decide) (choices 1) [2,4,32] r1850 c1850
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u127
  · exact u128
  · exact u129

def r1851 : Route 9 := (fun mask => (mask,id))

def c1851 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1851 : Upper (D 5) (R 5) [6,17,40,192,264,2] 13 := by
  apply FastRouting.sound _ _ [6,17,40,192,264,2] 13 (by decide) (choices 1) [1,4,32] r1851 c1851
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u130
  · exact u131
  · exact u132

def b1852 : PairBound 9 := { available := 35, camps := [{ cop := 3, region := 36, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 44 200 280 36 99 163 291), lower := (rows 7 19 44 200 280 36 64 128 256), losses := [] }

theorem u1852 : Upper (D 5) (R 5) [6,17,40,192,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1852
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 200, targets := 1 },{ cop := 0, region := 200, targets := 32 }], pairs := [(3,0),(3,5)], upper := (rows 7 19 44 200 304 33 78 142 270), lower := (rows 7 19 44 200 304 33 64 128 256), losses := [] }

theorem u1853 : Upper (D 5) (R 5) [6,17,40,192,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1853
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 13, camps := [{ cop := 0, region := 200, targets := 34 }], pairs := [(3,1),(3,5)], upper := (rows 7 19 44 200 304 34 77 141 269), lower := (rows 7 19 44 200 304 34 64 128 256), losses := [] }

theorem u1854 : Upper (D 5) (R 5) [6,17,40,192,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1854
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 11, camps := [{ cop := 0, region := 200, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 19 44 200 304 36 75 139 267), lower := (rows 7 19 44 200 304 36 64 128 256), losses := [] }

theorem u1855 : Upper (D 5) (R 5) [6,17,40,192,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1855
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 7, camps := [{ cop := 2, region := 275, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 19 44 200 304 40 71 135 263), lower := (rows 7 19 44 200 304 40 64 128 256), losses := [] }

theorem u1856 : Upper (D 5) (R 5) [6,17,40,192,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1856
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 268, camps := [{ cop := 3, region := 324, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 19 76 41 176 34 332 396 268), lower := (rows 7 19 76 41 176 34 64 128 256), losses := [] }

theorem u1857 : Upper (D 5) (R 5) [6,17,72,33,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1857
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 266, camps := [{ cop := 3, region := 402, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 19 76 41 176 36 330 394 266), lower := (rows 7 19 76 41 176 36 64 128 256), losses := [] }

theorem u1858 : Upper (D 5) (R 5) [6,17,72,33,160,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1858
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 40, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 7 19 76 41 176 40 326 390 262), lower := (rows 7 19 76 41 176 40 64 128 256), losses := [] }

theorem u1859 : Upper (D 5) (R 5) [6,17,72,33,160,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b1859
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P05
