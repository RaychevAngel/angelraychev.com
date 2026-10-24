import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P10C0011

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def r1800 : Route 9 := (fun mask => (mask,id))

def c1800 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | _ => 0)

theorem u1800 : Upper (D 10) (R 10) [6,96,384,33,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,160] 13 (by decide) (choices 1) [8,16,64,256] r1800 c1800
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u686
  · exact u687
  · exact u688
  · exact u689

def r1801 : Route 9 := (fun mask => (mask,id))

def c1801 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1801 : Upper (D 10) (R 10) [6,96,384,33,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,33,192] 13 (by decide) (choices 1) [8,16,256] r1801 c1801
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u690
  · exact u691
  · exact u692

def b1802 : PairBound 9 := { available := 120, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 98 388 41 400 120 120 248 376), lower := (rows 7 98 388 41 400 32 64 128 256), losses := [] }

theorem u1802 : Upper (D 10) (R 10) [6,96,384,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1802 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 24, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 98 388 56 56 481 449 449 449), lower := (rows 7 98 388 56 56 32 64 128 256), losses := [] }

theorem u1803 : Upper (D 10) (R 10) [6,96,384,48,40] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1803 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 424, camps := [{ cop := 4, region := 428, targets := 64 }], pairs := [(2,6),(3,6)], upper := (rows 7 98 388 56 81 424 488 424 424), lower := (rows 7 98 388 56 81 32 64 128 256), losses := [] }

theorem u1804 : Upper (D 10) (R 10) [6,96,384,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1804 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 417, camps := [{ cop := 1, region := 24, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 388 56 88 417 481 417 417), lower := (rows 7 98 388 56 88 32 64 128 256), losses := [] }

theorem u1805 : Upper (D 10) (R 10) [6,96,384,48,72] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1805 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 24, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 388 56 112 425 457 393 393), lower := (rows 7 98 388 56 112 32 64 128 256), losses := [] }

theorem u1806 : Upper (D 10) (R 10) [6,96,384,48,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1806 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 360, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 98 388 56 145 360 360 488 360), lower := (rows 7 98 388 56 145 32 64 128 256), losses := [] }

theorem u1807 : Upper (D 10) (R 10) [6,96,384,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1807 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 353, camps := [{ cop := 2, region := 99, targets := 128 }], pairs := [(0,7),(1,7)], upper := (rows 7 98 388 56 152 353 353 481 353), lower := (rows 7 98 388 56 152 32 64 128 256), losses := [] }

theorem u1808 : Upper (D 10) (R 10) [6,96,384,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1808 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 329, camps := [{ cop := 4, region := 8, targets := 192 }], pairs := [(3,6),(3,7)], upper := (rows 7 98 388 56 176 361 329 457 329), lower := (rows 7 98 388 56 176 32 64 128 256), losses := [] }

theorem u1809 : Upper (D 10) (R 10) [6,96,384,48,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1809 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1810 : Route 9 := (fun mask => (mask,id))

def c1810 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1810 : Upper (D 10) (R 10) [6,96,384,48,192] 13 := by
  apply FastRouting.sound _ _ [6,96,384,48,192] 13 (by decide) (choices 1) [1,8,256] r1810 c1810
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u693
  · exact u694
  · exact u695

def b1811 : PairBound 9 := { available := 105, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 98 388 56 400 105 105 233 361), lower := (rows 7 98 388 56 400 32 64 128 256), losses := [] }

theorem u1811 : Upper (D 10) (R 10) [6,96,384,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1811 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 304, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 388 73 152 304 368 432 304), lower := (rows 7 98 388 73 152 32 64 128 256), losses := [] }

theorem u1812 : Upper (D 10) (R 10) [6,96,384,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1812 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 312, camps := [{ cop := 3, region := 436, targets := 64 }], pairs := [(2,6),(4,6)], upper := (rows 7 98 388 73 176 312 376 440 312), lower := (rows 7 98 388 73 176 32 64 128 256), losses := [] }

theorem u1813 : Upper (D 10) (R 10) [6,96,384,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1813 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 296, camps := [{ cop := 4, region := 362, targets := 128 }], pairs := [(1,7),(3,7)], upper := (rows 7 98 388 88 145 296 360 424 296), lower := (rows 7 98 388 88 145 32 64 128 256), losses := [] }

theorem u1814 : Upper (D 10) (R 10) [6,96,384,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1814 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 389, targets := 64 }], pairs := [(0,6),(2,6)], upper := (rows 7 98 388 88 152 289 353 417 289), lower := (rows 7 98 388 88 152 32 64 128 256), losses := [] }

theorem u1815 : Upper (D 10) (R 10) [6,96,384,80,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1815 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1816 : Route 9 := (fun mask => (mask,id))

def c1816 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | _ => 0)

theorem u1816 : Upper (D 10) (R 10) [6,96,384,80,160] 13 := by
  apply FastRouting.sound _ _ [6,96,384,80,160] 13 (by decide) (choices 1) [1,8,256] r1816 c1816
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u696
  · exact u697
  · exact u698

def b1817 : PairBound 9 := { available := 41, camps := [{ cop := 2, region := 16, targets := 96 }], pairs := [(4,5),(4,6)], upper := (rows 7 98 388 88 400 41 105 169 297), lower := (rows 7 98 388 88 400 32 64 128 256), losses := [] }

theorem u1817 : Upper (D 10) (R 10) [6,96,384,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1817 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 388 104 152 305 369 433 305), lower := (rows 7 98 388 104 152 32 64 128 256), losses := [] }

theorem u1818 : Upper (D 10) (R 10) [6,96,384,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1818 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 281, camps := [{ cop := 1, region := 8, targets := 384 }], pairs := [(3,7),(3,8)], upper := (rows 7 98 388 104 176 313 345 409 281), lower := (rows 7 98 388 104 176 32 64 128 256), losses := [] }

theorem u1819 : Upper (D 10) (R 10) [6,96,384,96,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1819 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 112, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 98 388 137 280 112 112 240 368), lower := (rows 7 98 388 137 280 32 64 128 256), losses := [] }

theorem u1820 : Upper (D 10) (R 10) [6,96,384,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1820 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 120, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 98 388 137 304 120 120 248 376), lower := (rows 7 98 388 137 304 32 64 128 256), losses := [] }

theorem u1821 : Upper (D 10) (R 10) [6,96,384,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1821 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 56, camps := [{ cop := 3, region := 370, targets := 128 }], pairs := [(1,7),(4,7)], upper := (rows 7 98 388 137 336 56 120 184 312), lower := (rows 7 98 388 137 336 32 64 128 256), losses := [] }

theorem u1822 : Upper (D 10) (R 10) [6,96,384,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1822 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 97, camps := [{ cop := 2, region := 24, targets := 96 }], pairs := [(3,5),(3,6)], upper := (rows 7 98 388 152 280 97 97 225 353), lower := (rows 7 98 388 152 280 32 64 128 256), losses := [] }

theorem u1823 : Upper (D 10) (R 10) [6,96,384,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1823 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def r1824 : Route 9 := (fun mask => (mask,id))

def c1824 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1824 : Upper (D 10) (R 10) [6,96,384,144,288] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144,288] 13 (by decide) (choices 1) [1,8,64] r1824 c1824
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u699
  · exact u700
  · exact u701

def r1825 : Route 9 := (fun mask => (mask,id))

def c1825 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1825 : Upper (D 10) (R 10) [6,96,384,144,320] 13 := by
  apply FastRouting.sound _ _ [6,96,384,144,320] 13 (by decide) (choices 1) [1,8] r1825 c1825
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u702
  · exact u703

theorem m1826_16 : Upper (D 10) (R 10) [6,96,384,160,288,16] 13 :=
  permutation_upper _ _ _ [6,96,384,160,288,8] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 5 | 6 => 6 | 7 => 8 | _ => 7) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u705

def r1826 : Route 9 := (fun mask => (mask,id))

def c1826 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1826 : Upper (D 10) (R 10) [6,96,384,160,288] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160,288] 13 (by decide) (choices 1) [1,8,16,64] r1826 c1826
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact u704
  · exact u705
  · exact m1826_16
  · exact u706

def r1827 : Route 9 := (fun mask => (mask,id))

def c1827 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 64 => 6 | 128 => 7 | 256 => 8 | _ => 0)

theorem u1827 : Upper (D 10) (R 10) [6,96,384,160,320] 13 := by
  apply FastRouting.sound _ _ [6,96,384,160,320] 13 (by decide) (choices 1) [1,8,16] r1827 c1827
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u707
  · exact u708
  · exact u709

def b1828 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 41 280 304 368 432 304), lower := (rows 7 194 196 41 280 32 64 128 256), losses := [] }

theorem u1828 : Upper (D 10) (R 10) [6,192,192,33,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1828 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 41 304 312 376 440 312), lower := (rows 7 194 196 41 304 32 64 128 256), losses := [] }

theorem u1829 : Upper (D 10) (R 10) [6,192,192,33,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1829 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 296, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 56 273 296 360 424 296), lower := (rows 7 194 196 56 273 32 64 128 256), losses := [] }

theorem u1830 : Upper (D 10) (R 10) [6,192,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1830 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 289, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 56 280 289 353 417 289), lower := (rows 7 194 196 56 280 32 64 128 256), losses := [] }

theorem u1831 : Upper (D 10) (R 10) [6,192,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1831 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 5, targets := 288 }], pairs := [(0,5),(0,8)], upper := (rows 7 194 196 265 304 56 120 184 312), lower := (rows 7 194 196 265 304 32 64 128 256), losses := [] }

theorem u1832 : Upper (D 10) (R 10) [6,192,192,257,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1832 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 304, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 41 152 304 368 432 304), lower := (rows 7 194 324 41 152 32 64 128 256), losses := [] }

theorem u1833 : Upper (D 10) (R 10) [6,192,320,33,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1833 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 312, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 41 176 312 376 440 312), lower := (rows 7 194 324 41 176 32 64 128 256), losses := [] }

theorem u1834 : Upper (D 10) (R 10) [6,192,320,33,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1834 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 41 400 56 120 184 312), lower := (rows 7 194 324 41 400 32 64 128 256), losses := [] }

theorem u1835 : Upper (D 10) (R 10) [6,192,320,33,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1835 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 296, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 56 145 296 360 424 296), lower := (rows 7 194 324 56 145 32 64 128 256), losses := [] }

theorem u1836 : Upper (D 10) (R 10) [6,192,320,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1836 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 56 152 289 353 417 289), lower := (rows 7 194 324 56 152 32 64 128 256), losses := [] }

theorem u1837 : Upper (D 10) (R 10) [6,192,320,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1837 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 56 400 41 105 169 297), lower := (rows 7 194 324 56 400 32 64 128 256), losses := [] }

theorem u1838 : Upper (D 10) (R 10) [6,192,320,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1838 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 137 280 48 112 176 304), lower := (rows 7 194 324 137 280 32 64 128 256), losses := [] }

theorem u1839 : Upper (D 10) (R 10) [6,192,320,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1839 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 137 304 56 120 184 312), lower := (rows 7 194 324 137 304 32 64 128 256), losses := [] }

theorem u1840 : Upper (D 10) (R 10) [6,192,320,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1840 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 152 304 41 105 169 297), lower := (rows 7 194 324 152 304 32 64 128 256), losses := [] }

theorem u1841 : Upper (D 10) (R 10) [6,192,320,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1841 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 57, camps := [{ cop := 0, region := 440, targets := 64 }], pairs := [(3,6),(4,6)], upper := (rows 7 194 324 168 304 57 121 185 313), lower := (rows 7 194 324 168 304 32 64 128 256), losses := [] }

theorem u1842 : Upper (D 10) (R 10) [6,192,320,160,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1842 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 76 400 496 464 464 464), lower := (rows 35 35 44 76 400 32 64 128 256), losses := [] }

theorem u1843 : Upper (D 10) (R 10) [34,33,40,68,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1843 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 88 148 480 448 448 448), lower := (rows 35 35 44 88 148 32 64 128 256), losses := [] }

theorem u1844 : Upper (D 10) (R 10) [34,33,40,80,132] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1844 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 452, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 88 400 484 452 452 452), lower := (rows 35 35 44 88 400 32 64 128 256), losses := [] }

theorem u1845 : Upper (D 10) (R 10) [34,33,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1845 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 200 276 496 464 464 464), lower := (rows 35 35 44 200 276 32 64 128 256), losses := [] }

theorem u1846 : Upper (D 10) (R 10) [34,33,40,192,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1846 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 404, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 44 200 336 436 468 404 404), lower := (rows 35 35 44 200 336 32 64 128 256), losses := [] }

theorem u1847 : Upper (D 10) (R 10) [34,33,40,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1847 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 464, camps := [{ cop := 4, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 140 304 496 464 464 464), lower := (rows 35 35 76 140 304 32 64 128 256), losses := [] }

theorem u1848 : Upper (D 10) (R 10) [34,33,72,132,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1848 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 480, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 152 276 480 480 480 480), lower := (rows 35 35 76 152 276 32 64 128 256), losses := [] }

theorem u1849 : Upper (D 10) (R 10) [34,33,72,144,260] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1849 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 452, camps := [{ cop := 4, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 152 304 484 452 452 452), lower := (rows 35 35 76 152 304 32 64 128 256), losses := [] }

theorem u1850 : Upper (D 10) (R 10) [34,33,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1850 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 168 208 308 340 404 276), lower := (rows 35 35 76 168 208 32 64 128 256), losses := [] }

theorem u1851 : Upper (D 10) (R 10) [34,33,72,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1851 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 168 336 436 468 404 404), lower := (rows 35 35 76 168 336 32 64 128 256), losses := [] }

theorem u1852 : Upper (D 10) (R 10) [34,33,72,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1852 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 340, camps := [{ cop := 3, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 168 400 372 340 468 340), lower := (rows 35 35 76 168 400 32 64 128 256), losses := [] }

theorem u1853 : Upper (D 10) (R 10) [34,33,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1853 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 404, camps := [{ cop := 4, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 392 112 436 468 404 404), lower := (rows 35 35 76 392 112 32 64 128 256), losses := [] }

theorem u1854 : Upper (D 10) (R 10) [34,33,72,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1854 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 340, camps := [{ cop := 4, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 392 176 372 340 468 340), lower := (rows 35 35 76 392 176 32 64 128 256), losses := [] }

theorem u1855 : Upper (D 10) (R 10) [34,33,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1855 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 308, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 76 392 208 308 372 436 308), lower := (rows 35 35 76 392 208 32 64 128 256), losses := [] }

theorem u1856 : Upper (D 10) (R 10) [34,33,72,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1856 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 284, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 100 200 400 316 348 412 284), lower := (rows 35 35 100 200 400 32 64 128 256), losses := [] }

theorem u1857 : Upper (D 10) (R 10) [34,33,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1857 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 60, camps := [{ cop := 5, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 35 196 328 400 60 124 188 316), lower := (rows 35 35 196 328 400 32 64 128 256), losses := [] }

theorem u1858 : Upper (D 10) (R 10) [34,33,192,320,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1858 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 73 208 432 464 400 400), lower := (rows 35 38 44 73 208 32 64 128 256), losses := [] }

theorem u1859 : Upper (D 10) (R 10) [34,36,40,65,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1859 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P10
