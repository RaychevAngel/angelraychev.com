import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0004

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1800 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 133 200 280 33 83 147 275), lower := (rows 97 38 133 200 280 33 64 128 256), losses := [] }

theorem u1800 : Upper (D 3) (R 3) [96,36,129,192,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1800
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1801 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 133 200 280 34 81 145 273), lower := (rows 97 38 133 200 280 34 64 128 256), losses := [] }

theorem u1801 : Upper (D 3) (R 3) [96,36,129,192,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1801
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1802 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 133 200 280 48 67 131 259), lower := (rows 97 38 133 200 280 48 64 128 256), losses := [] }

theorem u1802 : Upper (D 3) (R 3) [96,36,129,192,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1802
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1803 : PairBound 9 := { available := 131, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 273 33 195 131 387), lower := (rows 97 38 140 88 273 33 64 128 256), losses := [] }

theorem u1803 : Upper (D 3) (R 3) [96,36,136,80,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1803
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1804 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 97 38 140 88 273 34 193 129 385), lower := (rows 97 38 140 88 273 34 64 128 256), losses := [] }

theorem u1804 : Upper (D 3) (R 3) [96,36,136,80,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1804
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1805 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 273 160 67 131 259), lower := (rows 97 38 140 88 273 160 64 128 256), losses := [] }

theorem u1805 : Upper (D 3) (R 3) [96,36,136,80,257,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1805
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1806 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 274 33 193 129 385), lower := (rows 97 38 140 88 274 33 64 128 256), losses := [] }

theorem u1806 : Upper (D 3) (R 3) [96,36,136,80,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1806
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1807 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 88 274 160 65 129 257), lower := (rows 97 38 140 88 274 160 64 128 256), losses := [] }

theorem u1807 : Upper (D 3) (R 3) [96,36,136,80,258,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1807
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1808 : PairBound 9 := { available := 82, camps := [{ cop := 6, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 265 145 33 82 210 338), lower := (rows 97 38 140 265 145 33 64 128 256), losses := [] }

theorem u1808 : Upper (D 3) (R 3) [96,36,136,257,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1808
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1809 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 140 265 145 34 81 209 337), lower := (rows 97 38 140 265 145 34 64 128 256), losses := [] }

theorem u1809 : Upper (D 3) (R 3) [96,36,136,257,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1809
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1810 : PairBound 9 := { available := 67, camps := [], pairs := [], upper := (rows 97 38 140 265 145 48 67 195 323), lower := (rows 97 38 140 265 145 48 64 128 256), losses := [] }

theorem u1810 : Upper (D 3) (R 3) [96,36,136,257,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1810
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1811 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 140 265 145 96 83 147 275), lower := (rows 97 38 140 265 145 96 64 128 256), losses := [] }

theorem u1811 : Upper (D 3) (R 3) [96,36,136,257,129,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1811
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1812 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 265 208 33 83 147 275), lower := (rows 97 38 140 265 208 33 64 128 256), losses := [] }

theorem u1812 : Upper (D 3) (R 3) [96,36,136,257,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1812
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1813 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 140 265 208 34 81 145 273), lower := (rows 97 38 140 265 208 34 64 128 256), losses := [] }

theorem u1813 : Upper (D 3) (R 3) [96,36,136,257,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1813
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1814 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 140 265 208 48 67 131 259), lower := (rows 97 38 140 265 208 48 64 128 256), losses := [] }

theorem u1814 : Upper (D 3) (R 3) [96,36,136,257,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1814
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1815 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 140 328 145 33 83 147 275), lower := (rows 97 38 140 328 145 33 64 128 256), losses := [] }

theorem u1815 : Upper (D 3) (R 3) [96,36,136,320,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1815
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1816 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 140 328 145 34 81 145 273), lower := (rows 97 38 140 328 145 34 64 128 256), losses := [] }

theorem u1816 : Upper (D 3) (R 3) [96,36,136,320,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1816
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1817 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 140 328 145 48 67 131 259), lower := (rows 97 38 140 328 145 48 64 128 256), losses := [] }

theorem u1817 : Upper (D 3) (R 3) [96,36,136,320,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1817
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1818 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 273 33 90 154 282), lower := (rows 97 38 196 137 273 33 64 128 256), losses := [] }

theorem u1818 : Upper (D 3) (R 3) [96,36,192,129,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1818
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1819 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 196 137 273 34 89 153 281), lower := (rows 97 38 196 137 273 34 64 128 256), losses := [] }

theorem u1819 : Upper (D 3) (R 3) [96,36,192,129,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1819
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1820 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 196 137 273 40 83 147 275), lower := (rows 97 38 196 137 273 40 64 128 256), losses := [] }

theorem u1820 : Upper (D 3) (R 3) [96,36,192,129,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1820
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1821 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 196 137 273 48 75 139 267), lower := (rows 97 38 196 137 273 48 64 128 256), losses := [] }

theorem u1821 : Upper (D 3) (R 3) [96,36,192,129,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1821
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1822 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 274 33 89 153 281), lower := (rows 97 38 196 137 274 33 64 128 256), losses := [] }

theorem u1822 : Upper (D 3) (R 3) [96,36,192,129,258,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1822
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1823 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 196 137 274 40 81 145 273), lower := (rows 97 38 196 137 274 40 64 128 256), losses := [] }

theorem u1823 : Upper (D 3) (R 3) [96,36,192,129,258,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1823
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1824 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 196 137 274 48 73 137 265), lower := (rows 97 38 196 137 274 48 64 128 256), losses := [] }

theorem u1824 : Upper (D 3) (R 3) [96,36,192,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1824
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1825 : PairBound 9 := { available := 19, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 137 280 33 83 147 275), lower := (rows 97 38 196 137 280 33 64 128 256), losses := [] }

theorem u1825 : Upper (D 3) (R 3) [96,36,192,129,264,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1825
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1826 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 196 137 280 34 81 145 273), lower := (rows 97 38 196 137 280 34 64 128 256), losses := [] }

theorem u1826 : Upper (D 3) (R 3) [96,36,192,129,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1826
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1827 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 196 137 280 48 67 131 259), lower := (rows 97 38 196 137 280 48 64 128 256), losses := [] }

theorem u1827 : Upper (D 3) (R 3) [96,36,192,129,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1827
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1828 : PairBound 9 := { available := 11, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 196 152 273 33 75 139 267), lower := (rows 97 38 196 152 273 33 64 128 256), losses := [] }

theorem u1828 : Upper (D 3) (R 3) [96,36,192,144,257,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1828
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1829 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 196 152 273 34 73 137 265), lower := (rows 97 38 196 152 273 34 64 128 256), losses := [] }

theorem u1829 : Upper (D 3) (R 3) [96,36,192,144,257,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1829
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1830 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 196 152 273 40 67 131 259), lower := (rows 97 38 196 152 273 40 64 128 256), losses := [] }

theorem u1830 : Upper (D 3) (R 3) [96,36,192,144,257,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1830
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1831 : PairBound 9 := { available := 88, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 137 146 33 88 216 344), lower := (rows 97 38 261 137 146 33 64 128 256), losses := [] }

theorem u1831 : Upper (D 3) (R 3) [96,36,257,129,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1831
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1832 : PairBound 9 := { available := 81, camps := [], pairs := [], upper := (rows 97 38 261 137 146 40 81 209 337), lower := (rows 97 38 261 137 146 40 64 128 256), losses := [] }

theorem u1832 : Upper (D 3) (R 3) [96,36,257,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1832
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1833 : PairBound 9 := { available := 73, camps := [], pairs := [], upper := (rows 97 38 261 137 146 48 73 201 329), lower := (rows 97 38 261 137 146 48 64 128 256), losses := [] }

theorem u1833 : Upper (D 3) (R 3) [96,36,257,129,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1833
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1834 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 137 146 96 89 153 281), lower := (rows 97 38 261 137 146 96 64 128 256), losses := [] }

theorem u1834 : Upper (D 3) (R 3) [96,36,257,129,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1834
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1835 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 137 208 33 90 154 282), lower := (rows 97 38 261 137 208 33 64 128 256), losses := [] }

theorem u1835 : Upper (D 3) (R 3) [96,36,257,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1835
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1836 : PairBound 9 := { available := 25, camps := [], pairs := [], upper := (rows 97 38 261 137 208 34 89 153 281), lower := (rows 97 38 261 137 208 34 64 128 256), losses := [] }

theorem u1836 : Upper (D 3) (R 3) [96,36,257,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1836
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1837 : PairBound 9 := { available := 19, camps := [], pairs := [], upper := (rows 97 38 261 137 208 40 83 147 275), lower := (rows 97 38 261 137 208 40 64 128 256), losses := [] }

theorem u1837 : Upper (D 3) (R 3) [96,36,257,129,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1837
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1838 : PairBound 9 := { available := 11, camps := [], pairs := [], upper := (rows 97 38 261 137 208 48 75 139 267), lower := (rows 97 38 261 137 208 48 64 128 256), losses := [] }

theorem u1838 : Upper (D 3) (R 3) [96,36,257,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1838
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1839 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 34, targets := 64 }], pairs := [(1,6)], upper := (rows 97 38 261 138 208 33 89 153 281), lower := (rows 97 38 261 138 208 33 64 128 256), losses := [] }

theorem u1839 : Upper (D 3) (R 3) [96,36,257,130,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1839
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1840 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 261 138 208 40 81 145 273), lower := (rows 97 38 261 138 208 40 64 128 256), losses := [] }

theorem u1840 : Upper (D 3) (R 3) [96,36,257,130,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1840
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1841 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 261 138 208 48 73 137 265), lower := (rows 97 38 261 138 208 48 64 128 256), losses := [] }

theorem u1841 : Upper (D 3) (R 3) [96,36,257,130,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1841
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1842 : PairBound 9 := { available := 19, camps := [{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 137 208 33 83 147 275), lower := (rows 97 38 268 137 208 33 64 128 256), losses := [] }

theorem u1842 : Upper (D 3) (R 3) [96,36,264,129,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1842
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1843 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 268 137 208 34 81 145 273), lower := (rows 97 38 268 137 208 34 64 128 256), losses := [] }

theorem u1843 : Upper (D 3) (R 3) [96,36,264,129,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1843
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1844 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 268 137 208 48 67 131 259), lower := (rows 97 38 268 137 208 48 64 128 256), losses := [] }

theorem u1844 : Upper (D 3) (R 3) [96,36,264,129,192,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1844
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1845 : PairBound 9 := { available := 19, camps := [{ cop := 3, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 268 200 145 33 83 147 275), lower := (rows 97 38 268 200 145 33 64 128 256), losses := [] }

theorem u1845 : Upper (D 3) (R 3) [96,36,264,192,129,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1845
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1846 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 268 200 145 34 81 145 273), lower := (rows 97 38 268 200 145 34 64 128 256), losses := [] }

theorem u1846 : Upper (D 3) (R 3) [96,36,264,192,129,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1846
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1847 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 268 200 145 48 67 131 259), lower := (rows 97 38 268 200 145 48 64 128 256), losses := [] }

theorem u1847 : Upper (D 3) (R 3) [96,36,264,192,129,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1847
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1848 : PairBound 9 := { available := 25, camps := [{ cop := 2, region := 33, targets := 128 }], pairs := [(0,7)], upper := (rows 97 38 324 137 146 33 89 153 281), lower := (rows 97 38 324 137 146 33 64 128 256), losses := [] }

theorem u1848 : Upper (D 3) (R 3) [96,36,320,129,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1848
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1849 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 324 137 146 40 81 145 273), lower := (rows 97 38 324 137 146 40 64 128 256), losses := [] }

theorem u1849 : Upper (D 3) (R 3) [96,36,320,129,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1849
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1850 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 97 38 324 137 146 48 73 137 265), lower := (rows 97 38 324 137 146 48 64 128 256), losses := [] }

theorem u1850 : Upper (D 3) (R 3) [96,36,320,129,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1850
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1851 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 259 7 28 41 81 96 224 160 416), lower := (rows 259 7 28 41 81 96 64 128 256), losses := [] }

theorem u1851 : Upper (D 3) (R 3) [258,5,24,33,65,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1851
    (constants 3).1 (constants 3).2 (by decide +kernel)

theorem m1852_32 : Upper (D 3) (R 3) [258,5,24,33,65,128,32] 13 :=
  permutation_upper _ _ _ [258,5,24,33,65,64,128] (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) (fun i => match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 4 | 4 => 3 | 5 => 6 | 6 => 5 | 7 => 7 | _ => 8) 13
    ((PermutationNine.check_true _ _ _ _ _ _).mp (by decide +kernel)) u290

def r1852 : Route 9 := (fun mask => (mask,id))

def c1852 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 256 => 8 | _ => 0)

theorem u1852 : Upper (D 3) (R 3) [258,5,24,33,65,128] 13 := by
  apply FastRouting.sound _ _ [258,5,24,33,65,128] 13 (by decide) (choices 1) [32,128] r1852 c1852
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact m1852_32
  · exact u291

def b1853 : PairBound 9 := { available := 224, camps := [{ cop := 0, region := 40, targets := 64 }], pairs := [(3,6)], upper := (rows 259 7 28 41 208 33 224 224 480), lower := (rows 259 7 28 41 208 33 64 128 256), losses := [] }

theorem u1853 : Upper (D 3) (R 3) [258,5,24,33,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1853
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1854 : PairBound 9 := { available := 161, camps := [], pairs := [(0,6)], upper := (rows 259 7 28 41 208 96 225 161 417), lower := (rows 259 7 28 41 208 96 64 128 256), losses := [{ target := 6, region := (rows 5 6 4 8 16 32 0 136 264), good := (rows 259 7 415 425 144 32 0 128 256) }] }

theorem u1854 : Upper (D 3) (R 3) [258,5,24,33,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1854
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1855 : PairBound 9 := { available := 224, camps := [{ cop := 3, region := 38, targets := 64 }], pairs := [(1,6)], upper := (rows 259 7 44 25 208 33 224 224 480), lower := (rows 259 7 44 25 208 33 64 128 256), losses := [] }

theorem u1855 : Upper (D 3) (R 3) [258,5,40,17,192,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1855
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1856 : PairBound 9 := { available := 161, camps := [{ cop := 2, region := 387, targets := 64 }], pairs := [(0,6)], upper := (rows 259 7 44 25 208 96 225 161 417), lower := (rows 259 7 44 25 208 96 64 128 256), losses := [] }

theorem u1856 : Upper (D 3) (R 3) [258,5,40,17,192,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1856
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1857 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 38, targets := 128 }], pairs := [(1,7)], upper := (rows 259 7 44 73 112 33 208 144 400), lower := (rows 259 7 44 73 112 33 64 128 256), losses := [] }

theorem u1857 : Upper (D 3) (R 3) [258,5,40,65,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1857
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b1858 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 44 73 112 48 193 129 385), lower := (rows 259 7 44 73 112 48 64 128 256), losses := [] }

theorem u1858 : Upper (D 3) (R 3) [258,5,40,65,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b1858
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r1859 : Route 9 := (fun mask => (mask,id))

def c1859 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 256 => 8 | _ => 0)

theorem u1859 : Upper (D 3) (R 3) [258,5,40,65,96,128] 13 := by
  apply FastRouting.sound _ _ [258,5,40,65,96,128] 13 (by decide) (choices 1) [1,16,128] r1859 c1859
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u292
  · exact u293
  · exact u294

#print axioms u1859
end Delivery.IrregularNine14.P03
