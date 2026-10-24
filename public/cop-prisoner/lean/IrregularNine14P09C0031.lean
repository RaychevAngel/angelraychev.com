import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 273 288 68 144 400), lower := (rows 35 194 44 73 273 288 68 128 256), losses := [] }

theorem u1860 : Upper (D 9) (R 9) [34,192,40,65,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1860 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 422, targets := 1 },{ cop := 3, region := 436, targets := 64 }], pairs := [(1,0),(2,0),(2,6),(4,6)], upper := (rows 35 194 44 73 273 288 80 132 388), lower := (rows 35 194 44 73 273 288 80 128 256), losses := [] }

theorem u1861 : Upper (D 9) (R 9) [34,192,40,65,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1861 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1862 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 73 273 288 192 148 276), lower := (rows 35 194 44 73 273 288 192 128 256), losses := [] }

theorem u1862 : Upper (D 9) (R 9) [34,192,40,65,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1862 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 276 288 65 144 400), lower := (rows 35 194 44 73 276 288 65 128 256), losses := [] }

theorem u1863 : Upper (D 9) (R 9) [34,192,40,65,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1863 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 436, targets := 64 },{ cop := 1, region := 289, targets := 64 },{ cop := 3, region := 130, targets := 32 }], pairs := [(0,6),(1,5),(2,6),(4,6)], upper := (rows 35 194 44 73 276 288 80 129 385), lower := (rows 35 194 44 73 276 288 80 128 256), losses := [] }

theorem u1864 : Upper (D 9) (R 9) [34,192,40,65,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1864 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 73 276 288 192 145 273), lower := (rows 35 194 44 73 276 288 192 128 256), losses := [] }

theorem u1865 : Upper (D 9) (R 9) [34,192,40,65,260,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1865 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 3, region := 438, targets := 1 }], pairs := [(1,0),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 400 288 65 148 276), lower := (rows 35 194 44 73 400 288 65 128 256), losses := [] }

theorem u1866 : Upper (D 9) (R 9) [34,192,40,65,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1866 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 384 }], pairs := [(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 73 400 288 68 145 273), lower := (rows 35 194 44 73 400 288 68 128 256), losses := [] }

theorem u1867 : Upper (D 9) (R 9) [34,192,40,65,384,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1867 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 3, region := 292, targets := 64 }], pairs := [(0,7),(2,6),(2,7),(3,7)], upper := (rows 35 194 44 73 400 288 80 133 261), lower := (rows 35 194 44 73 400 288 80 128 256), losses := [] }

theorem u1868 : Upper (D 9) (R 9) [34,192,40,65,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1868 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1869 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 76, targets := 384 },{ cop := 0, region := 466, targets := 32 }], pairs := [(1,5),(2,7),(2,8),(3,7),(3,8)], upper := (rows 35 194 44 76 400 288 65 145 273), lower := (rows 35 194 44 76 400 288 65 128 256), losses := [] }

theorem u1869 : Upper (D 9) (R 9) [34,192,40,68,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1869 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 44 76 400 288 80 129 257), lower := (rows 35 194 44 76 400 288 80 128 256), losses := [] }

theorem u1870 : Upper (D 9) (R 9) [34,192,40,68,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1870 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 74, targets := 288 },{ cop := 3, region := 422, targets := 1 }], pairs := [(1,0),(1,5),(1,8),(3,5),(3,8)], upper := (rows 35 194 44 88 145 288 65 388 260), lower := (rows 35 194 44 88 145 288 65 128 256), losses := [] }

theorem u1871 : Upper (D 9) (R 9) [34,192,40,80,129,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1871 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 4, region := 364, targets := 128 }], pairs := [(0,6),(2,7),(3,7),(4,6)], upper := (rows 35 194 44 88 145 288 68 385 257), lower := (rows 35 194 44 88 145 288 68 128 256), losses := [] }

theorem u1872 : Upper (D 9) (R 9) [34,192,40,80,129,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1872 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 364, targets := 128 }], pairs := [(0,6),(2,0),(2,6),(2,7),(3,7)], upper := (rows 35 194 44 88 145 288 320 133 261), lower := (rows 35 194 44 88 145 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 352 352 128 256), good := (rows 98 226 108 124 144 352 352 128 352) },{ target := 6, region := (rows 3 2 12 8 18 352 0 128 256), good := (rows 51 179 44 60 145 288 288 128 288) }] }

theorem u1873 : Upper (D 9) (R 9) [34,192,40,80,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1873 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(2,6),(4,6)], upper := (rows 35 194 44 88 148 288 65 385 257), lower := (rows 35 194 44 88 148 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 12 8 24 363 0 195 323), good := (rows 419 419 60 444 148 288 417 128 288) }] }

theorem u1874 : Upper (D 9) (R 9) [34,192,40,80,132,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1874 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 1, camps := [{ cop := 0, region := 450, targets := 32 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(1,5),(2,0),(3,0)], upper := (rows 35 194 44 88 148 288 320 129 257), lower := (rows 35 194 44 88 148 288 320 128 256), losses := [{ target := 0, region := (rows 0 2 15 11 18 352 352 128 256), good := (rows 126 254 108 124 148 352 352 128 352) }] }

theorem u1875 : Upper (D 9) (R 9) [34,192,40,80,132,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1875 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 260, camps := [{ cop := 4, region := 111, targets := 256 },{ cop := 2, region := 400, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,8),(4,0)], upper := (rows 35 194 44 88 400 33 65 388 260), lower := (rows 35 194 44 88 400 33 65 128 256), losses := [] }

theorem u1876 : Upper (D 9) (R 9) [34,192,40,80,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1876 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 257, camps := [{ cop := 4, region := 111, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 35 194 44 88 400 33 68 385 257), lower := (rows 35 194 44 88 400 33 68 128 256), losses := [] }

theorem u1877 : Upper (D 9) (R 9) [34,192,40,80,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1877 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 33 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 88 400 33 320 133 261), lower := (rows 35 194 44 88 400 33 320 128 256), losses := [] }

theorem u1878 : Upper (D 9) (R 9) [34,192,40,80,384,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1878 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 400, targets := 97 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(4,0),(4,5),(4,6)], upper := (rows 35 194 44 328 148 33 65 400 272), lower := (rows 35 194 44 328 148 33 65 128 256), losses := [] }

theorem u1879 : Upper (D 9) (R 9) [34,192,40,320,132,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1879 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 44 328 148 33 80 385 257), lower := (rows 35 194 44 328 148 33 80 128 256), losses := [] }

theorem u1880 : Upper (D 9) (R 9) [34,192,40,320,132,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1880 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 183, targets := 256 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0),(4,8)], upper := (rows 35 194 44 328 148 33 320 145 273), lower := (rows 35 194 44 328 148 33 320 128 256), losses := [] }

theorem u1881 : Upper (D 9) (R 9) [34,192,40,320,132,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1881 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 144, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(4,6)], upper := (rows 35 194 44 328 273 33 68 144 400), lower := (rows 35 194 44 328 273 33 68 128 256), losses := [] }

theorem u1882 : Upper (D 9) (R 9) [34,192,40,320,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1882 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 3, region := 167, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,8)], upper := (rows 35 194 44 328 273 33 80 132 388), lower := (rows 35 194 44 328 273 33 80 128 256), losses := [] }

theorem u1883 : Upper (D 9) (R 9) [34,192,40,320,257,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1883 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 6, region := 2, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 328 273 33 192 148 276), lower := (rows 35 194 44 328 273 33 192 128 256), losses := [] }

theorem u1884 : Upper (D 9) (R 9) [34,192,40,320,257,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1884 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 132, camps := [{ cop := 2, region := 195, targets := 256 },{ cop := 4, region := 108, targets := 128 }], pairs := [(0,8),(1,8),(2,7),(3,7)], upper := (rows 35 194 44 328 273 48 65 132 388), lower := (rows 35 194 44 328 273 48 65 128 256), losses := [] }

theorem u1885 : Upper (D 9) (R 9) [34,192,40,320,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1885 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 108, targets := 129 }], pairs := [(2,0),(2,7),(3,0)], upper := (rows 35 194 44 328 273 48 68 129 385), lower := (rows 35 194 44 328 273 48 68 128 256), losses := [] }

theorem u1886 : Upper (D 9) (R 9) [34,192,40,320,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1886 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 328 273 48 192 133 261), lower := (rows 35 194 44 328 273 48 192 128 256), losses := [] }

theorem u1887 : Upper (D 9) (R 9) [34,192,40,320,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1887 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 400, targets := 97 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(4,0),(4,5),(4,6)], upper := (rows 35 194 44 328 276 33 65 144 400), lower := (rows 35 194 44 328 276 33 65 128 256), losses := [] }

theorem u1888 : Upper (D 9) (R 9) [34,192,40,320,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1888 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 129, camps := [{ cop := 3, region := 167, targets := 256 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,8),(1,8),(2,8),(3,0)], upper := (rows 35 194 44 328 276 33 80 129 385), lower := (rows 35 194 44 328 276 33 80 128 256), losses := [] }

theorem u1889 : Upper (D 9) (R 9) [34,192,40,320,260,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1889 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1890 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 317, targets := 128 },{ cop := 4, region := 227, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(3,7),(4,7)], upper := (rows 35 194 44 328 276 33 192 145 273), lower := (rows 35 194 44 328 276 33 192 128 256), losses := [] }

theorem u1890 : Upper (D 9) (R 9) [34,192,40,320,260,1,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1890 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1891 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 400, targets := 97 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,7),(0,8),(4,0),(4,5),(4,6)], upper := (rows 35 194 44 328 400 33 65 148 276), lower := (rows 35 194 44 328 400 33 65 128 256), losses := [] }

theorem u1891 : Upper (D 9) (R 9) [34,192,40,320,384,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1891 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 305, targets := 64 },{ cop := 1, region := 33, targets := 384 }], pairs := [(0,6),(0,7),(0,8),(4,6)], upper := (rows 35 194 44 328 400 33 68 145 273), lower := (rows 35 194 44 328 400 33 68 128 256), losses := [] }

theorem u1892 : Upper (D 9) (R 9) [34,192,40,320,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1892 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 74, targets := 33 }], pairs := [(1,0),(1,5),(3,0),(3,5)], upper := (rows 35 194 44 328 400 33 80 133 261), lower := (rows 35 194 44 328 400 33 80 128 256), losses := [] }

theorem u1893 : Upper (D 9) (R 9) [34,192,40,320,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1893 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 288 }], pairs := [(1,5),(1,8),(2,5),(2,8)], upper := (rows 35 194 69 137 276 288 72 176 304), lower := (rows 35 194 69 137 276 288 72 128 256), losses := [] }

theorem u1894 : Upper (D 9) (R 9) [34,192,65,129,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1894 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 297, targets := 64 },{ cop := 3, region := 372, targets := 128 }], pairs := [(0,6),(2,7),(3,6),(4,7)], upper := (rows 35 194 69 137 276 288 80 168 296), lower := (rows 35 194 69 137 276 288 80 128 256), losses := [] }

theorem u1895 : Upper (D 9) (R 9) [34,192,65,129,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1895 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 69 137 276 288 96 152 280), lower := (rows 35 194 69 137 276 288 96 128 256), losses := [] }

theorem u1896 : Upper (D 9) (R 9) [34,192,65,129,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1896 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 288, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 140 273 48 72 416 288), lower := (rows 35 194 69 140 273 48 72 128 256), losses := [] }

theorem u1897 : Upper (D 9) (R 9) [34,192,65,132,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1897 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1898 : PairBound 9 := { available := 264, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 194 69 140 273 48 96 392 264), lower := (rows 35 194 69 140 273 48 96 128 256), losses := [] }

theorem u1898 : Upper (D 9) (R 9) [34,192,65,132,257,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1898 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 4, region := 68, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(2,5),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 140 273 48 320 168 296), lower := (rows 35 194 69 140 273 48 320 128 256), losses := [] }

theorem u1899 : Upper (D 9) (R 9) [34,192,65,132,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1899 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 35 194 69 140 273 288 72 176 304), lower := (rows 35 194 69 140 273 288 72 128 256), losses := [] }

theorem u1900 : Upper (D 9) (R 9) [34,192,65,132,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1900 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 40, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 2, region := 440, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,6)], upper := (rows 35 194 69 140 273 288 80 168 296), lower := (rows 35 194 69 140 273 288 80 128 256), losses := [] }

theorem u1901 : Upper (D 9) (R 9) [34,192,65,132,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1901 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 24, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 69 140 273 288 96 152 280), lower := (rows 35 194 69 140 273 288 96 128 256), losses := [] }

theorem u1902 : Upper (D 9) (R 9) [34,192,65,132,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1902 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 288, camps := [{ cop := 2, region := 442, targets := 1 },{ cop := 6, region := 4, targets := 32 }], pairs := [(1,0),(2,5),(3,0),(4,0)], upper := (rows 35 194 69 140 280 48 65 416 288), lower := (rows 35 194 69 140 280 48 65 128 256), losses := [] }

theorem u1903 : Upper (D 9) (R 9) [34,192,65,132,264,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1903 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 2, region := 392, targets := 64 }], pairs := [(1,5),(3,5),(3,6),(4,5)], upper := (rows 35 194 69 140 280 48 96 385 257), lower := (rows 35 194 69 140 280 48 96 128 256), losses := [] }

theorem u1904 : Upper (D 9) (R 9) [34,192,65,132,264,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1904 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 0, region := 324, targets := 128 }], pairs := [(1,8),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 140 280 48 320 161 289), lower := (rows 35 194 69 140 280 48 320 128 256), losses := [{ target := 8, region := (rows 1 6 4 12 16 48 64 129 0), good := (rows 163 194 207 142 56 48 64 128 0) }] }

theorem u1905 : Upper (D 9) (R 9) [34,192,65,132,264,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1905 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 194 69 140 280 288 65 176 304), lower := (rows 35 194 69 140 280 288 65 128 256), losses := [] }

theorem u1906 : Upper (D 9) (R 9) [34,192,65,132,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1906 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 140 280 288 80 161 289), lower := (rows 35 194 69 140 280 288 80 128 256), losses := [] }

theorem u1907 : Upper (D 9) (R 9) [34,192,65,132,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1907 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 69 140 280 288 96 145 273), lower := (rows 35 194 69 140 280 288 96 128 256), losses := [] }

theorem u1908 : Upper (D 9) (R 9) [34,192,65,132,264,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1908 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(2,5),(2,7),(2,8)], upper := (rows 35 194 69 152 273 288 68 168 296), lower := (rows 35 194 69 152 273 288 68 128 256), losses := [] }

theorem u1909 : Upper (D 9) (R 9) [34,192,65,144,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1909 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 35 194 69 152 273 288 72 164 292), lower := (rows 35 194 69 152 273 288 72 128 256), losses := [] }

theorem u1910 : Upper (D 9) (R 9) [34,192,65,144,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1910 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 69 152 273 288 96 140 268), lower := (rows 35 194 69 152 273 288 96 128 256), losses := [] }

theorem u1911 : Upper (D 9) (R 9) [34,192,65,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1911 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 194 69 152 276 288 65 168 296), lower := (rows 35 194 69 152 276 288 65 128 256), losses := [] }

theorem u1912 : Upper (D 9) (R 9) [34,192,65,144,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1912 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(4,7)], upper := (rows 35 194 69 152 276 288 72 161 289), lower := (rows 35 194 69 152 276 288 72 128 256), losses := [] }

theorem u1913 : Upper (D 9) (R 9) [34,192,65,144,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1913 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 384 }], pairs := [(1,5),(2,7),(2,8),(3,5),(4,5)], upper := (rows 35 194 69 152 276 288 96 137 265), lower := (rows 35 194 69 152 276 288 96 128 256), losses := [] }

theorem u1914 : Upper (D 9) (R 9) [34,192,65,144,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1914 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 68, targets := 416 }], pairs := [(2,5),(2,7),(2,8)], upper := (rows 35 194 69 168 273 48 68 392 264), lower := (rows 35 194 69 168 273 48 68 128 256), losses := [] }

theorem u1915 : Upper (D 9) (R 9) [34,192,65,160,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1915 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 260, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 168 273 48 72 388 260), lower := (rows 35 194 69 168 273 48 72 128 256), losses := [] }

theorem u1916 : Upper (D 9) (R 9) [34,192,65,160,257,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1916 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 4, region := 68, targets := 32 },{ cop := 4, region := 68, targets := 128 }], pairs := [(2,5),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 168 273 48 320 140 268), lower := (rows 35 194 69 168 273 48 320 128 256), losses := [] }

theorem u1917 : Upper (D 9) (R 9) [34,192,65,160,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1917 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(2,5),(2,7),(2,8)], upper := (rows 35 194 69 168 273 288 68 152 280), lower := (rows 35 194 69 168 273 288 68 128 256), losses := [] }

theorem u1918 : Upper (D 9) (R 9) [34,192,65,160,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1918 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 20, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(4,7)], upper := (rows 35 194 69 168 273 288 72 148 276), lower := (rows 35 194 69 168 273 288 72 128 256), losses := [] }

theorem u1919 : Upper (D 9) (R 9) [34,192,65,160,257,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1919 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P09
