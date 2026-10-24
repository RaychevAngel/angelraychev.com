import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 104, targets := 3 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(3,1)], upper := (rows 11 19 133 44 304 96 68 194 322), lower := (rows 11 19 133 44 304 96 68 128 256), losses := [] }

theorem u1860 : Upper (D 6) (R 6) [10,17,129,36,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1860
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 36, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 133 44 336 96 66 164 292), lower := (rows 11 19 133 44 336 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 21 119 67 140 268), good := (rows 506 114 508 444 368 96 98 128 256) },{ target := 1, region := (rows 1 0 7 74 112 112 64 202 330), good := (rows 397 445 133 444 504 504 508 128 256) }] }

theorem u1861 : Upper (D 6) (R 6) [10,17,129,36,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1861
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1862 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 104, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 133 44 336 96 68 162 290), lower := (rows 11 19 133 44 336 96 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 21 125 76 131 259), good := (rows 506 434 508 124 376 104 124 128 256) }] }

theorem u1862 : Upper (D 6) (R 6) [10,17,129,36,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1862
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 19 133 44 336 96 96 134 262), lower := (rows 11 19 133 44 336 96 96 128 256), losses := [] }

theorem u1863 : Upper (D 6) (R 6) [10,17,129,36,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1863
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2)], upper := (rows 11 19 133 104 52 288 66 196 324), lower := (rows 11 19 133 104 52 288 66 128 256), losses := [] }

theorem u1864 : Upper (D 6) (R 6) [10,17,129,96,36,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1864
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 19 133 104 52 288 68 194 322), lower := (rows 11 19 133 104 52 288 68 128 256), losses := [] }

theorem u1865 : Upper (D 6) (R 6) [10,17,129,96,36,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1865
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 96, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 133 104 276 34 68 224 352), lower := (rows 11 19 133 104 276 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 84 35 84 142 270), good := (rows 426 506 508 504 476 426 476 128 256) },{ target := 1, region := (rows 1 0 5 40 17 32 87 168 296), good := (rows 477 85 213 488 340 488 68 128 256) }] }

theorem u1866 : Upper (D 6) (R 6) [10,17,129,96,260,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1866
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 19 133 104 276 34 96 196 324), lower := (rows 11 19 133 104 276 34 96 128 256), losses := [] }

theorem u1867 : Upper (D 6) (R 6) [10,17,129,96,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1867
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 407, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 19 133 104 276 36 96 194 322), lower := (rows 11 19 133 104 276 36 96 128 256), losses := [] }

theorem u1868 : Upper (D 6) (R 6) [10,17,129,96,260,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1868
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1869 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 75, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 104 304 36 66 196 324), lower := (rows 11 19 133 104 304 36 66 128 256), losses := [] }

theorem u1869 : Upper (D 6) (R 6) [10,17,129,96,288,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1869
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 275, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 133 104 304 36 68 194 322), lower := (rows 11 19 133 104 304 36 68 128 256), losses := [] }

theorem u1870 : Upper (D 6) (R 6) [10,17,129,96,288,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1870
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 96, camps := [], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 133 268 52 96 66 224 352), lower := (rows 11 19 133 268 52 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 28 103 67 231 359), good := (rows 506 506 508 444 444 480 482 128 256) },{ target := 1, region := (rows 1 0 4 24 16 96 64 224 352), good := (rows 9 25 133 268 444 480 480 128 256) }] }

theorem u1871 : Upper (D 6) (R 6) [10,17,129,260,36,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1871
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 19 133 268 52 96 96 194 322), lower := (rows 11 19 133 268 52 96 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 12 28 511 511 131 259), good := (rows 506 498 508 380 124 96 96 224 352) }] }

theorem u1872 : Upper (D 6) (R 6) [10,17,129,260,36,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1872
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 96, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 133 268 112 34 68 224 352), lower := (rows 11 19 133 268 112 34 68 128 256), losses := [{ target := 0, region := (rows 0 2 4 76 21 35 76 149 277), good := (rows 506 434 508 476 504 34 476 128 256) },{ target := 1, region := (rows 1 0 6 42 48 32 111 176 304), good := (rows 77 477 197 332 504 508 68 128 256) }] }

theorem u1873 : Upper (D 6) (R 6) [10,17,129,260,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1873
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 68, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 19 133 268 112 34 96 196 324), lower := (rows 11 19 133 268 112 34 96 128 256), losses := [] }

theorem u1874 : Upper (D 6) (R 6) [10,17,129,260,96,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1874
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 19 133 268 112 36 96 194 322), lower := (rows 11 19 133 268 112 36 96 128 256), losses := [] }

theorem u1875 : Upper (D 6) (R 6) [10,17,129,260,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1875
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(3,0),(4,0)], upper := (rows 11 19 133 296 52 96 66 196 324), lower := (rows 11 19 133 296 52 96 66 128 256), losses := [{ target := 0, region := (rows 0 2 4 28 20 103 67 132 260), good := (rows 106 122 508 296 444 96 98 128 256) }] }

theorem u1876 : Upper (D 6) (R 6) [10,17,129,288,36,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1876
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 },{ cop := 0, region := 196, targets := 32 }], pairs := [(2,5),(4,0),(4,1)], upper := (rows 11 19 133 296 52 96 68 194 322), lower := (rows 11 19 133 296 52 96 68 128 256), losses := [] }

theorem u1877 : Upper (D 6) (R 6) [10,17,129,288,36,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1877
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 296 84 34 68 224 352), lower := (rows 11 19 133 296 84 34 68 128 256), losses := [] }

theorem u1878 : Upper (D 6) (R 6) [10,17,129,288,68,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1878
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 68, camps := [], pairs := [(2,1),(3,0),(4,0)], upper := (rows 11 19 133 296 84 34 96 196 324), lower := (rows 11 19 133 296 84 34 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 20 35 111 148 276), good := (rows 106 506 508 360 476 106 96 128 256) },{ target := 1, region := (rows 1 0 7 104 49 32 104 177 305), good := (rows 477 405 405 504 476 508 504 128 256) }] }

theorem u1879 : Upper (D 6) (R 6) [10,17,129,288,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1879
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 96, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 4, region := 296, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 19 133 296 84 36 66 224 352), lower := (rows 11 19 133 296 84 36 66 128 256), losses := [] }

theorem u1880 : Upper (D 6) (R 6) [10,17,129,288,68,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1880
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 112, targets := 3 }], pairs := [(3,0),(4,0),(4,1)], upper := (rows 11 19 133 296 84 36 96 194 322), lower := (rows 11 19 133 296 84 36 96 128 256), losses := [{ target := 0, region := (rows 0 2 4 14 52 52 126 131 259), good := (rows 458 506 508 376 124 124 112 128 256) }] }

theorem u1881 : Upper (D 6) (R 6) [10,17,129,288,68,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1881
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 82, targets := 32 },{ cop := 4, region := 296, targets := 1 }], pairs := [(1,5),(3,0),(4,5)], upper := (rows 11 19 133 296 84 96 66 164 292), lower := (rows 11 19 133 296 84 96 66 128 256), losses := [] }

theorem u1882 : Upper (D 6) (R 6) [10,17,129,288,68,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1882
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 299, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 296 84 96 68 162 290), lower := (rows 11 19 133 296 84 96 68 128 256), losses := [] }

theorem u1883 : Upper (D 6) (R 6) [10,17,129,288,68,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1883
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 19 133 296 84 96 96 134 262), lower := (rows 11 19 133 296 84 96 96 128 256), losses := [] }

theorem u1884 : Upper (D 6) (R 6) [10,17,129,288,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1884
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 83, targets := 4 }], pairs := [(0,2),(1,2),(4,2)], upper := (rows 11 19 133 296 112 36 66 196 324), lower := (rows 11 19 133 296 112 36 66 128 256), losses := [] }

theorem u1885 : Upper (D 6) (R 6) [10,17,129,288,96,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1885
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 267, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 133 296 112 36 68 194 322), lower := (rows 11 19 133 296 112 36 68 128 256), losses := [] }

theorem u1886 : Upper (D 6) (R 6) [10,17,129,288,96,4,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1886
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 304 96 66 196 324), lower := (rows 11 19 164 13 304 96 66 128 256), losses := [] }

theorem u1887 : Upper (D 6) (R 6) [10,17,160,5,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1887
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 304 96 68 194 322), lower := (rows 11 19 164 13 304 96 68 128 256), losses := [] }

theorem u1888 : Upper (D 6) (R 6) [10,17,160,5,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1888
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 336 96 66 164 292), lower := (rows 11 19 164 13 336 96 66 128 256), losses := [] }

theorem u1889 : Upper (D 6) (R 6) [10,17,160,5,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1889
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1890 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 13 336 96 68 162 290), lower := (rows 11 19 164 13 336 96 68 128 256), losses := [] }

theorem u1890 : Upper (D 6) (R 6) [10,17,160,5,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1890
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1891 : PairBound 9 := { available := 6, camps := [{ cop := 8, region := 112, targets := 7 }], pairs := [(4,0),(4,1),(4,2)], upper := (rows 11 19 164 13 336 96 96 134 262), lower := (rows 11 19 164 13 336 96 96 128 256), losses := [] }

theorem u1891 : Upper (D 6) (R 6) [10,17,160,5,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1891
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 68, camps := [{ cop := 5, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 41 276 96 66 196 324), lower := (rows 11 19 164 41 276 96 66 128 256), losses := [] }

theorem u1892 : Upper (D 6) (R 6) [10,17,160,33,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1892
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 41 276 96 68 194 322), lower := (rows 11 19 164 41 276 96 68 128 256), losses := [] }

theorem u1893 : Upper (D 6) (R 6) [10,17,160,33,260,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1893
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 73 276 96 66 164 292), lower := (rows 11 19 164 73 276 96 66 128 256), losses := [] }

theorem u1894 : Upper (D 6) (R 6) [10,17,160,65,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1894
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 164 73 276 96 68 162 290), lower := (rows 11 19 164 73 276 96 68 128 256), losses := [] }

theorem u1895 : Upper (D 6) (R 6) [10,17,160,65,260,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1895
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 107, targets := 4 }], pairs := [(0,2),(1,2),(3,2)], upper := (rows 11 19 164 73 276 96 96 134 262), lower := (rows 11 19 164 73 276 96 96 128 256), losses := [] }

theorem u1896 : Upper (D 6) (R 6) [10,17,160,65,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1896
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 4, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 73 304 96 66 132 260), lower := (rows 11 19 164 73 304 96 66 128 256), losses := [] }

theorem u1897 : Upper (D 6) (R 6) [10,17,160,65,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1897
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1898 : PairBound 9 := { available := 6, camps := [{ cop := 0, region := 500, targets := 1 },{ cop := 7, region := 100, targets := 2 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 73 304 96 68 134 262), lower := (rows 11 19 164 73 304 96 68 128 256), losses := [] }

theorem u1898 : Upper (D 6) (R 6) [10,17,160,65,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1898
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 420, targets := 65 }], pairs := [(2,0),(2,6)], upper := (rows 11 19 164 76 112 288 65 134 262), lower := (rows 11 19 164 76 112 288 65 128 256), losses := [] }

theorem u1899 : Upper (D 6) (R 6) [10,17,160,68,96,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1899
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 420, targets := 66 }], pairs := [(2,1),(2,6)], upper := (rows 11 19 164 76 112 288 66 133 261), lower := (rows 11 19 164 76 112 288 66 128 256), losses := [] }

theorem u1900 : Upper (D 6) (R 6) [10,17,160,68,96,256,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1900
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 19 164 76 112 288 68 131 259), lower := (rows 11 19 164 76 112 288 68 128 256), losses := [] }

theorem u1901 : Upper (D 6) (R 6) [10,17,160,68,96,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1901
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 140, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 164 76 274 96 65 164 292), lower := (rows 11 19 164 76 274 96 65 128 256), losses := [] }

theorem u1902 : Upper (D 6) (R 6) [10,17,160,68,258,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1902
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 33, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 164 76 274 96 68 161 289), lower := (rows 11 19 164 76 274 96 68 128 256), losses := [] }

theorem u1903 : Upper (D 6) (R 6) [10,17,160,68,258,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1903
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 275, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 76 274 96 96 133 261), lower := (rows 11 19 164 76 274 96 96 128 256), losses := [] }

theorem u1904 : Upper (D 6) (R 6) [10,17,160,68,258,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1904
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 164 76 276 33 66 224 352), lower := (rows 11 19 164 76 276 33 66 128 256), losses := [] }

theorem u1905 : Upper (D 6) (R 6) [10,17,160,68,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1905
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 164 76 276 33 96 194 322), lower := (rows 11 19 164 76 276 33 96 128 256), losses := [] }

theorem u1906 : Upper (D 6) (R 6) [10,17,160,68,260,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1906
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 96, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 164 76 276 34 65 224 352), lower := (rows 11 19 164 76 276 34 65 128 256), losses := [] }

theorem u1907 : Upper (D 6) (R 6) [10,17,160,68,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1907
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 65, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 164 76 276 34 96 193 321), lower := (rows 11 19 164 76 276 34 96 128 256), losses := [] }

theorem u1908 : Upper (D 6) (R 6) [10,17,160,68,260,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1908
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 34, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 164 76 276 96 65 162 290), lower := (rows 11 19 164 76 276 96 65 128 256), losses := [] }

theorem u1909 : Upper (D 6) (R 6) [10,17,160,68,260,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1909
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 75, targets := 32 }], pairs := [(0,5),(1,5),(3,5)], upper := (rows 11 19 164 76 276 96 66 161 289), lower := (rows 11 19 164 76 276 96 66 128 256), losses := [] }

theorem u1910 : Upper (D 6) (R 6) [10,17,160,68,260,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1910
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 275, targets := 96 }], pairs := [(0,5),(0,6),(1,5)], upper := (rows 11 19 164 76 276 96 96 131 259), lower := (rows 11 19 164 76 276 96 96 128 256), losses := [] }

theorem u1911 : Upper (D 6) (R 6) [10,17,160,68,260,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1911
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 19 164 76 304 33 66 196 324), lower := (rows 11 19 164 76 304 33 66 128 256), losses := [{ target := 0, region := (rows 0 2 52 42 52 32 67 170 298), good := (rows 458 478 444 476 444 508 458 128 256) }] }

theorem u1912 : Upper (D 6) (R 6) [10,17,160,68,288,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1912
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 19 164 76 304 33 68 194 322), lower := (rows 11 19 164 76 304 33 68 128 256), losses := [] }

theorem u1913 : Upper (D 6) (R 6) [10,17,160,68,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1913
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 68, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 19 164 76 304 34 65 196 324), lower := (rows 11 19 164 76 304 34 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 72 81 35 64 200 328), good := (rows 446 54 164 476 304 34 508 128 256) }] }

theorem u1914 : Upper (D 6) (R 6) [10,17,160,68,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1914
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 19 164 76 304 34 68 193 321), lower := (rows 11 19 164 76 304 34 68 128 256), losses := [] }

theorem u1915 : Upper (D 6) (R 6) [10,17,160,68,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1915
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 6, camps := [], pairs := [(2,0),(3,0),(4,0)], upper := (rows 11 19 164 76 304 96 65 134 262), lower := (rows 11 19 164 76 304 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 69 104 81 104 64 131 259), good := (rows 446 406 172 124 312 124 508 128 256) }] }

theorem u1916 : Upper (D 6) (R 6) [10,17,160,68,288,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1916
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 5, camps := [], pairs := [(2,1),(3,1),(4,1)], upper := (rows 11 19 164 76 304 96 66 133 261), lower := (rows 11 19 164 76 304 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 69 104 81 104 64 131 259), good := (rows 445 405 172 124 312 124 508 128 256) }] }

theorem u1917 : Upper (D 6) (R 6) [10,17,160,68,288,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1917
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 3, camps := [{ cop := 7, region := 108, targets := 3 }], pairs := [(2,0),(2,1),(3,0)], upper := (rows 11 19 164 76 304 96 68 131 259), lower := (rows 11 19 164 76 304 96 68 128 256), losses := [] }

theorem u1918 : Upper (D 6) (R 6) [10,17,160,68,288,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1918
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 336 33 66 164 292), lower := (rows 11 19 164 76 336 33 66 128 256), losses := [] }

theorem u1919 : Upper (D 6) (R 6) [10,17,160,68,320,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1919
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P06
