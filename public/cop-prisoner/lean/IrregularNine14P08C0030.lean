import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P08
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 35 14 69 392 176 48 97 225 353), lower := (rows 35 14 69 392 176 48 64 128 256), losses := [] }

theorem u1800 : Upper (D 8) (R 8) [34,12,65,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1800 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 408, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 69 392 176 96 113 177 305), lower := (rows 35 14 69 392 176 96 64 128 256), losses := [] }

theorem u1801 : Upper (D 8) (R 8) [34,12,65,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1801 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 35 14 69 392 208 33 112 176 304), lower := (rows 35 14 69 392 208 33 64 128 256), losses := [] }

theorem u1802 : Upper (D 8) (R 8) [34,12,65,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1802 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 14 69 392 208 48 97 161 289), lower := (rows 35 14 69 392 208 48 64 128 256), losses := [] }

theorem u1803 : Upper (D 8) (R 8) [34,12,65,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1803 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 273 33 224 224 480), lower := (rows 35 14 84 168 273 33 64 128 256), losses := [] }

theorem u1804 : Upper (D 8) (R 8) [34,12,80,160,257,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1804 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 168 273 96 225 161 417), lower := (rows 35 14 84 168 273 96 64 128 256), losses := [] }

theorem u1805 : Upper (D 8) (R 8) [34,12,80,160,257,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1805 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 168 273 160 97 225 353), lower := (rows 35 14 84 168 273 160 64 128 256), losses := [] }

theorem u1806 : Upper (D 8) (R 8) [34,12,80,160,257,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1806 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 168 304 33 193 193 449), lower := (rows 35 14 84 168 304 33 64 128 256), losses := [] }

theorem u1807 : Upper (D 8) (R 8) [34,12,80,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1807 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 136, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 168 304 96 193 129 385), lower := (rows 35 14 84 168 304 96 64 128 256), losses := [] }

theorem u1808 : Upper (D 8) (R 8) [34,12,80,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1808 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 168 304 160 65 193 321), lower := (rows 35 14 84 168 304 160 64 128 256), losses := [] }

theorem u1809 : Upper (D 8) (R 8) [34,12,80,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1809 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1810 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 84 265 176 33 224 224 480), lower := (rows 35 14 84 265 176 33 64 128 256), losses := [] }

theorem u1810 : Upper (D 8) (R 8) [34,12,80,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1810 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 265 176 96 225 161 417), lower := (rows 35 14 84 265 176 96 64 128 256), losses := [] }

theorem u1811 : Upper (D 8) (R 8) [34,12,80,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1811 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 265 176 160 97 225 353), lower := (rows 35 14 84 265 176 160 64 128 256), losses := [] }

theorem u1812 : Upper (D 8) (R 8) [34,12,80,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1812 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 296 145 33 224 224 480), lower := (rows 35 14 84 296 145 33 64 128 256), losses := [] }

theorem u1813 : Upper (D 8) (R 8) [34,12,80,288,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1813 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 296 145 96 225 161 417), lower := (rows 35 14 84 296 145 96 64 128 256), losses := [] }

theorem u1814 : Upper (D 8) (R 8) [34,12,80,288,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1814 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 328, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 84 296 145 160 97 225 353), lower := (rows 35 14 84 296 145 160 64 128 256), losses := [] }

theorem u1815 : Upper (D 8) (R 8) [34,12,80,288,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1815 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 84 296 176 33 193 193 449), lower := (rows 35 14 84 296 176 33 64 128 256), losses := [] }

theorem u1816 : Upper (D 8) (R 8) [34,12,80,288,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1816 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 392, targets := 64 }], pairs := [(3,6)], upper := (rows 35 14 84 296 176 96 193 129 385), lower := (rows 35 14 84 296 176 96 64 128 256), losses := [] }

theorem u1817 : Upper (D 8) (R 8) [34,12,80,288,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1817 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 84 296 176 160 65 193 321), lower := (rows 35 14 84 296 176 160 64 128 256), losses := [] }

theorem u1818 : Upper (D 8) (R 8) [34,12,80,288,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1818 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 208, camps := [{ cop := 0, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 100 265 176 33 208 208 464), lower := (rows 35 14 100 265 176 33 64 128 256), losses := [] }

theorem u1819 : Upper (D 8) (R 8) [34,12,96,257,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1819 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 14 100 265 176 48 193 193 449), lower := (rows 35 14 100 265 176 48 64 128 256), losses := [] }

theorem u1820 : Upper (D 8) (R 8) [34,12,96,257,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1820 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 145, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 265 176 96 209 145 401), lower := (rows 35 14 100 265 176 96 64 128 256), losses := [] }

theorem u1821 : Upper (D 8) (R 8) [34,12,96,257,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1821 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 81, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 100 265 176 160 81 209 337), lower := (rows 35 14 100 265 176 160 64 128 256), losses := [] }

theorem u1822 : Upper (D 8) (R 8) [34,12,96,257,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1822 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 100 265 208 33 240 176 432), lower := (rows 35 14 100 265 208 33 64 128 256), losses := [] }

theorem u1823 : Upper (D 8) (R 8) [34,12,96,257,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1823 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 100 265 208 48 225 161 417), lower := (rows 35 14 100 265 208 48 64 128 256), losses := [] }

theorem u1824 : Upper (D 8) (R 8) [34,12,96,257,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1824 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 49, camps := [{ cop := 4, region := 36, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 100 265 208 160 113 177 305), lower := (rows 35 14 100 265 208 160 64 128 256), losses := [] }

theorem u1825 : Upper (D 8) (R 8) [34,12,96,257,192,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1825 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 224, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 145 33 224 224 480), lower := (rows 35 14 100 280 145 33 64 128 256), losses := [] }

theorem u1826 : Upper (D 8) (R 8) [34,12,96,272,129,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1826 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 145 96 225 161 417), lower := (rows 35 14 100 280 145 96 64 128 256), losses := [] }

theorem u1827 : Upper (D 8) (R 8) [34,12,96,272,129,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1827 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 97, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 14 100 280 145 160 97 225 353), lower := (rows 35 14 100 280 145 160 64 128 256), losses := [] }

theorem u1828 : Upper (D 8) (R 8) [34,12,96,272,129,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1828 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 193, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 176 33 193 193 449), lower := (rows 35 14 100 280 176 33 64 128 256), losses := [] }

theorem u1829 : Upper (D 8) (R 8) [34,12,96,272,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1829 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 129, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 280 176 96 193 129 385), lower := (rows 35 14 100 280 176 96 64 128 256), losses := [] }

theorem u1830 : Upper (D 8) (R 8) [34,12,96,272,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1830 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 335, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 100 280 176 160 65 193 321), lower := (rows 35 14 100 280 176 160 64 128 256), losses := [] }

theorem u1831 : Upper (D 8) (R 8) [34,12,96,272,160,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1831 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 392 176 33 81 209 337), lower := (rows 35 14 100 392 176 33 64 128 256), losses := [] }

theorem u1832 : Upper (D 8) (R 8) [34,12,96,384,160,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1832 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 14 100 392 176 48 65 193 321), lower := (rows 35 14 100 392 176 48 64 128 256), losses := [] }

theorem u1833 : Upper (D 8) (R 8) [34,12,96,384,160,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1833 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 411, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 392 176 96 81 145 273), lower := (rows 35 14 100 392 176 96 64 128 256), losses := [] }

theorem u1834 : Upper (D 8) (R 8) [34,12,96,384,160,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1834 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 100 392 208 33 113 177 305), lower := (rows 35 14 100 392 208 33 64 128 256), losses := [] }

theorem u1835 : Upper (D 8) (R 8) [34,12,96,384,192,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1835 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 14 100 392 208 48 97 161 289), lower := (rows 35 14 100 392 208 48 64 128 256), losses := [] }

theorem u1836 : Upper (D 8) (R 8) [34,12,96,384,192,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1836 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 176, camps := [{ cop := 0, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 35 14 196 265 112 33 240 176 432), lower := (rows 35 14 196 265 112 33 64 128 256), losses := [] }

theorem u1837 : Upper (D 8) (R 8) [34,12,192,257,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1837 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 14 196 265 112 48 225 161 417), lower := (rows 35 14 196 265 112 48 64 128 256), losses := [] }

theorem u1838 : Upper (D 8) (R 8) [34,12,192,257,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1838 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 196 265 112 160 113 177 305), lower := (rows 35 14 196 265 112 160 64 128 256), losses := [] }

theorem u1839 : Upper (D 8) (R 8) [34,12,192,257,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1839 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6)], upper := (rows 35 14 196 296 112 33 209 145 401), lower := (rows 35 14 196 296 112 33 64 128 256), losses := [] }

theorem u1840 : Upper (D 8) (R 8) [34,12,192,288,96,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1840 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 196 296 112 48 193 129 385), lower := (rows 35 14 196 296 112 48 64 128 256), losses := [] }

theorem u1841 : Upper (D 8) (R 8) [34,12,192,288,96,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1841 [(5,4)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 344, targets := 128 }], pairs := [(3,7)], upper := (rows 35 14 196 296 112 160 81 145 273), lower := (rows 35 14 196 296 112 160 64 128 256), losses := [] }

theorem u1842 : Upper (D 8) (R 8) [34,12,192,288,96,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1842 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 400 33 224 224 480), lower := (rows 35 67 28 44 400 33 64 128 256), losses := [] }

theorem u1843 : Upper (D 8) (R 8) [34,65,24,36,384,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1843 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 44 400 96 225 161 417), lower := (rows 35 67 28 44 400 96 64 128 256), losses := [] }

theorem u1844 : Upper (D 8) (R 8) [34,65,24,36,384,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1844 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 44 400 160 97 225 353), lower := (rows 35 67 28 44 400 160 64 128 256), losses := [] }

theorem u1845 : Upper (D 8) (R 8) [34,65,24,36,384,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1845 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 140 304 33 224 224 480), lower := (rows 35 67 28 140 304 33 64 128 256), losses := [] }

theorem u1846 : Upper (D 8) (R 8) [34,65,24,132,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1846 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 140 304 96 225 161 417), lower := (rows 35 67 28 140 304 96 64 128 256), losses := [] }

theorem u1847 : Upper (D 8) (R 8) [34,65,24,132,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1847 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 97, camps := [{ cop := 5, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 140 304 160 97 225 353), lower := (rows 35 67 28 140 304 160 64 128 256), losses := [] }

theorem u1848 : Upper (D 8) (R 8) [34,65,24,132,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1848 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 168 276 33 224 224 480), lower := (rows 35 67 28 168 276 33 64 128 256), losses := [] }

theorem u1849 : Upper (D 8) (R 8) [34,65,24,160,260,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1849 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 161, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 168 276 96 225 161 417), lower := (rows 35 67 28 168 276 96 64 128 256), losses := [] }

theorem u1850 : Upper (D 8) (R 8) [34,65,24,160,260,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1850 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 97, camps := [{ cop := 3, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 276 160 97 225 353), lower := (rows 35 67 28 168 276 160 64 128 256), losses := [] }

theorem u1851 : Upper (D 8) (R 8) [34,65,24,160,260,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1851 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1852 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 168 304 33 196 196 452), lower := (rows 35 67 28 168 304 33 64 128 256), losses := [] }

theorem u1852 : Upper (D 8) (R 8) [34,65,24,160,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1852 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1853 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 35 67 28 168 304 36 193 193 449), lower := (rows 35 67 28 168 304 36 64 128 256), losses := [] }

theorem u1853 : Upper (D 8) (R 8) [34,65,24,160,288,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1853 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 412, targets := 64 }], pairs := [(2,6)], upper := (rows 35 67 28 168 304 96 197 133 389), lower := (rows 35 67 28 168 304 96 64 128 256), losses := [] }

theorem u1854 : Upper (D 8) (R 8) [34,65,24,160,288,64] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1854 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 69, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 304 160 69 197 325), lower := (rows 35 67 28 168 304 160 64 128 256), losses := [] }

theorem u1855 : Upper (D 8) (R 8) [34,65,24,160,288,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1855 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 168 336 33 228 164 420), lower := (rows 35 67 28 168 336 33 64 128 256), losses := [] }

theorem u1856 : Upper (D 8) (R 8) [34,65,24,160,320,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1856 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 35 67 28 168 336 36 225 161 417), lower := (rows 35 67 28 168 336 36 64 128 256), losses := [] }

theorem u1857 : Upper (D 8) (R 8) [34,65,24,160,320,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1857 [(5,2)]
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 37, camps := [{ cop := 3, region := 343, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 28 168 336 160 101 165 293), lower := (rows 35 67 28 168 336 160 64 128 256), losses := [] }

theorem u1858 : Upper (D 8) (R 8) [34,65,24,160,320,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1858 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

def b1859 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 476, targets := 1 }], pairs := [(2,0)], upper := (rows 35 67 28 200 304 33 228 164 420), lower := (rows 35 67 28 200 304 33 64 128 256), losses := [] }

theorem u1859 : Upper (D 8) (R 8) [34,65,24,192,288,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 8) 14 b1859 []
    (constants 8).1 (constants 8).2 (by decide +kernel)

#print axioms u1859
end Delivery.IrregularNine14.P08
