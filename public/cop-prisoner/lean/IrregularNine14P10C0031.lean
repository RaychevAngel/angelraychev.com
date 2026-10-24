import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P10
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1860 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 73 400 496 464 464 464), lower := (rows 35 38 44 73 400 32 64 128 256), losses := [] }

theorem u1860 : Upper (D 10) (R 10) [34,36,40,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1860 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1861 : PairBound 9 := { available := 448, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 88 145 480 448 448 448), lower := (rows 35 38 44 88 145 32 64 128 256), losses := [] }

theorem u1861 : Upper (D 10) (R 10) [34,36,40,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1861 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1862 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 88 400 481 449 449 449), lower := (rows 35 38 44 88 400 32 64 128 256), losses := [] }

theorem u1862 : Upper (D 10) (R 10) [34,36,40,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1862 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1863 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 200 81 432 464 400 400), lower := (rows 35 38 44 200 81 32 64 128 256), losses := [] }

theorem u1863 : Upper (D 10) (R 10) [34,36,40,192,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1863 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1864 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 200 273 496 464 464 464), lower := (rows 35 38 44 200 273 32 64 128 256), losses := [] }

theorem u1864 : Upper (D 10) (R 10) [34,36,40,192,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1864 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1865 : PairBound 9 := { available := 401, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 44 200 336 433 465 401 401), lower := (rows 35 38 44 200 336 32 64 128 256), losses := [] }

theorem u1865 : Upper (D 10) (R 10) [34,36,40,192,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1865 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1866 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 56 152 480 448 448 448), lower := (rows 35 38 69 56 152 32 64 128 256), losses := [] }

theorem u1866 : Upper (D 10) (R 10) [34,36,65,48,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1866 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1867 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 56 208 424 456 392 392), lower := (rows 35 38 69 56 208 32 64 128 256), losses := [] }

theorem u1867 : Upper (D 10) (R 10) [34,36,65,48,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1867 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1868 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 56 400 488 456 456 456), lower := (rows 35 38 69 56 400 32 64 128 256), losses := [] }

theorem u1868 : Upper (D 10) (R 10) [34,36,65,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1868 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1869 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 88 176 424 456 392 392), lower := (rows 35 38 69 88 176 32 64 128 256), losses := [] }

theorem u1869 : Upper (D 10) (R 10) [34,36,65,80,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1869 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1870 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 88 400 424 488 424 424), lower := (rows 35 38 69 88 400 32 64 128 256), losses := [] }

theorem u1870 : Upper (D 10) (R 10) [34,36,65,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1870 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1871 : PairBound 9 := { available := 400, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 69 104 152 432 464 400 400), lower := (rows 35 38 69 104 152 32 64 128 256), losses := [] }

theorem u1871 : Upper (D 10) (R 10) [34,36,65,96,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1871 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1872 : PairBound 9 := { available := 408, camps := [{ cop := 3, region := 7, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 69 104 400 440 472 408 408), lower := (rows 35 38 69 104 400 32 64 128 256), losses := [] }

theorem u1872 : Upper (D 10) (R 10) [34,36,65,96,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1872 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1873 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 152 280 480 480 480 480), lower := (rows 35 38 69 152 280 32 64 128 256), losses := [] }

theorem u1873 : Upper (D 10) (R 10) [34,36,65,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1873 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1874 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 152 304 488 456 456 456), lower := (rows 35 38 69 152 304 32 64 128 256), losses := [] }

theorem u1874 : Upper (D 10) (R 10) [34,36,65,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1874 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1875 : PairBound 9 := { available := 424, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 152 336 424 488 424 424), lower := (rows 35 38 69 152 336 32 64 128 256), losses := [] }

theorem u1875 : Upper (D 10) (R 10) [34,36,65,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1875 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1876 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 168 208 312 344 408 280), lower := (rows 35 38 69 168 208 32 64 128 256), losses := [] }

theorem u1876 : Upper (D 10) (R 10) [34,36,65,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1876 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1877 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 168 336 440 472 408 408), lower := (rows 35 38 69 168 336 32 64 128 256), losses := [] }

theorem u1877 : Upper (D 10) (R 10) [34,36,65,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1877 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1878 : PairBound 9 := { available := 344, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 168 400 376 344 472 344), lower := (rows 35 38 69 168 400 32 64 128 256), losses := [] }

theorem u1878 : Upper (D 10) (R 10) [34,36,65,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1878 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1879 : PairBound 9 := { available := 312, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 69 200 400 312 376 440 312), lower := (rows 35 38 69 200 400 32 64 128 256), losses := [] }

theorem u1879 : Upper (D 10) (R 10) [34,36,65,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1879 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1880 : PairBound 9 := { available := 448, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 56 145 480 448 448 448), lower := (rows 35 38 76 56 145 32 64 128 256), losses := [] }

theorem u1880 : Upper (D 10) (R 10) [34,36,72,48,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1880 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1881 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 56 400 481 449 449 449), lower := (rows 35 38 76 56 400 32 64 128 256), losses := [] }

theorem u1881 : Upper (D 10) (R 10) [34,36,72,48,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1881 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1882 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 112 432 464 400 400), lower := (rows 35 38 76 137 112 32 64 128 256), losses := [] }

theorem u1882 : Upper (D 10) (R 10) [34,36,72,129,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1882 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1883 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 176 368 336 464 336), lower := (rows 35 38 76 137 176 32 64 128 256), losses := [] }

theorem u1883 : Upper (D 10) (R 10) [34,36,72,129,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1883 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1884 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 208 304 368 432 304), lower := (rows 35 38 76 137 208 32 64 128 256), losses := [] }

theorem u1884 : Upper (D 10) (R 10) [34,36,72,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1884 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1885 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 304 496 464 464 464), lower := (rows 35 38 76 137 304 32 64 128 256), losses := [] }

theorem u1885 : Upper (D 10) (R 10) [34,36,72,129,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1885 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1886 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 336 432 496 432 432), lower := (rows 35 38 76 137 336 32 64 128 256), losses := [] }

theorem u1886 : Upper (D 10) (R 10) [34,36,72,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1886 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1887 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 137 400 368 368 496 368), lower := (rows 35 38 76 137 400 32 64 128 256), losses := [] }

theorem u1887 : Upper (D 10) (R 10) [34,36,72,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1887 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1888 : PairBound 9 := { available := 480, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 152 273 480 480 480 480), lower := (rows 35 38 76 152 273 32 64 128 256), losses := [] }

theorem u1888 : Upper (D 10) (R 10) [34,36,72,144,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1888 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1889 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 152 304 481 449 449 449), lower := (rows 35 38 76 152 304 32 64 128 256), losses := [] }

theorem u1889 : Upper (D 10) (R 10) [34,36,72,144,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1889 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1890 : PairBound 9 := { available := 400, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 81 432 464 400 400), lower := (rows 35 38 76 168 81 32 64 128 256), losses := [] }

theorem u1890 : Upper (D 10) (R 10) [34,36,72,160,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1890 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1891 : PairBound 9 := { available := 336, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 145 368 336 464 336), lower := (rows 35 38 76 168 145 32 64 128 256), losses := [] }

theorem u1891 : Upper (D 10) (R 10) [34,36,72,160,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1891 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1892 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 208 305 337 401 273), lower := (rows 35 38 76 168 208 32 64 128 256), losses := [] }

theorem u1892 : Upper (D 10) (R 10) [34,36,72,160,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1892 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1893 : PairBound 9 := { available := 464, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 273 496 464 464 464), lower := (rows 35 38 76 168 273 32 64 128 256), losses := [] }

theorem u1893 : Upper (D 10) (R 10) [34,36,72,160,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1893 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1894 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 336 433 465 401 401), lower := (rows 35 38 76 168 336 32 64 128 256), losses := [] }

theorem u1894 : Upper (D 10) (R 10) [34,36,72,160,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1894 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1895 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 168 400 369 337 465 337), lower := (rows 35 38 76 168 400 32 64 128 256), losses := [] }

theorem u1895 : Upper (D 10) (R 10) [34,36,72,160,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1895 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1896 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 81 432 496 432 432), lower := (rows 35 38 76 392 81 32 64 128 256), losses := [] }

theorem u1896 : Upper (D 10) (R 10) [34,36,72,384,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1896 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1897 : PairBound 9 := { available := 401, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 112 433 465 401 401), lower := (rows 35 38 76 392 112 32 64 128 256), losses := [] }

theorem u1897 : Upper (D 10) (R 10) [34,36,72,384,96] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1897 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1898 : PairBound 9 := { available := 368, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 145 368 368 496 368), lower := (rows 35 38 76 392 145 32 64 128 256), losses := [] }

theorem u1898 : Upper (D 10) (R 10) [34,36,72,384,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1898 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1899 : PairBound 9 := { available := 337, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 176 369 337 465 337), lower := (rows 35 38 76 392 176 32 64 128 256), losses := [] }

theorem u1899 : Upper (D 10) (R 10) [34,36,72,384,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1899 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1900 : PairBound 9 := { available := 305, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 76 392 208 305 369 433 305), lower := (rows 35 38 76 392 208 32 64 128 256), losses := [] }

theorem u1900 : Upper (D 10) (R 10) [34,36,72,384,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1900 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1901 : PairBound 9 := { available := 400, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 100 73 152 432 464 400 400), lower := (rows 35 38 100 73 152 32 64 128 256), losses := [] }

theorem u1901 : Upper (D 10) (R 10) [34,36,96,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1901 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1902 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 384 }], pairs := [(0,7),(0,8)], upper := (rows 35 38 100 73 400 440 472 408 408), lower := (rows 35 38 100 73 400 32 64 128 256), losses := [] }

theorem u1902 : Upper (D 10) (R 10) [34,36,96,65,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1902 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1903 : PairBound 9 := { available := 392, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 88 145 424 456 392 392), lower := (rows 35 38 100 88 145 32 64 128 256), losses := [] }

theorem u1903 : Upper (D 10) (R 10) [34,36,96,80,129] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1903 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1904 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 88 400 425 457 393 393), lower := (rows 35 38 100 88 400 32 64 128 256), losses := [] }

theorem u1904 : Upper (D 10) (R 10) [34,36,96,80,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1904 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1905 : PairBound 9 := { available := 280, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 137 208 312 344 408 280), lower := (rows 35 38 100 137 208 32 64 128 256), losses := [] }

theorem u1905 : Upper (D 10) (R 10) [34,36,96,129,192] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1905 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1906 : PairBound 9 := { available := 464, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 137 280 496 464 464 464), lower := (rows 35 38 100 137 280 32 64 128 256), losses := [] }

theorem u1906 : Upper (D 10) (R 10) [34,36,96,129,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1906 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1907 : PairBound 9 := { available := 408, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 137 336 440 472 408 408), lower := (rows 35 38 100 137 336 32 64 128 256), losses := [] }

theorem u1907 : Upper (D 10) (R 10) [34,36,96,129,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1907 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1908 : PairBound 9 := { available := 344, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 137 400 376 344 472 344), lower := (rows 35 38 100 137 400 32 64 128 256), losses := [] }

theorem u1908 : Upper (D 10) (R 10) [34,36,96,129,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1908 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1909 : PairBound 9 := { available := 449, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 152 280 481 449 449 449), lower := (rows 35 38 100 152 280 32 64 128 256), losses := [] }

theorem u1909 : Upper (D 10) (R 10) [34,36,96,144,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1909 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1910 : PairBound 9 := { available := 393, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 152 336 425 457 393 393), lower := (rows 35 38 100 152 336 32 64 128 256), losses := [] }

theorem u1910 : Upper (D 10) (R 10) [34,36,96,144,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1910 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1911 : PairBound 9 := { available := 281, camps := [{ cop := 2, region := 3, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 100 200 400 313 345 409 281), lower := (rows 35 38 100 200 400 32 64 128 256), losses := [] }

theorem u1911 : Upper (D 10) (R 10) [34,36,96,192,384] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1911 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1912 : PairBound 9 := { available := 392, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 56 81 424 456 392 392), lower := (rows 35 38 196 56 81 32 64 128 256), losses := [] }

theorem u1912 : Upper (D 10) (R 10) [34,36,192,48,65] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1912 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1913 : PairBound 9 := { available := 456, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 56 273 488 456 456 456), lower := (rows 35 38 196 56 273 32 64 128 256), losses := [] }

theorem u1913 : Upper (D 10) (R 10) [34,36,192,48,257] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1913 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1914 : PairBound 9 := { available := 449, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 56 280 481 449 449 449), lower := (rows 35 38 196 56 280 32 64 128 256), losses := [] }

theorem u1914 : Upper (D 10) (R 10) [34,36,192,48,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1914 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1915 : PairBound 9 := { available := 393, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 56 336 425 457 393 393), lower := (rows 35 38 196 56 336 32 64 128 256), losses := [] }

theorem u1915 : Upper (D 10) (R 10) [34,36,192,48,320] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1915 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1916 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 152 304 368 432 304), lower := (rows 35 38 196 73 152 32 64 128 256), losses := [] }

theorem u1916 : Upper (D 10) (R 10) [34,36,192,65,136] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1916 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1917 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 176 312 344 408 280), lower := (rows 35 38 196 73 176 32 64 128 256), losses := [] }

theorem u1917 : Upper (D 10) (R 10) [34,36,192,65,160] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1917 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1918 : PairBound 9 := { available := 432, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 280 432 496 432 432), lower := (rows 35 38 196 73 280 32 64 128 256), losses := [] }

theorem u1918 : Upper (D 10) (R 10) [34,36,192,65,264] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1918 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

def b1919 : PairBound 9 := { available := 408, camps := [{ cop := 1, region := 1, targets := 192 }], pairs := [(0,6),(0,7)], upper := (rows 35 38 196 73 304 440 472 408 408), lower := (rows 35 38 196 73 304 32 64 128 256), losses := [] }

theorem u1919 : Upper (D 10) (R 10) [34,36,192,65,288] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 10) 14 b1919 []
    (constants 10).1 (constants 10).2 (by decide +kernel)

#print axioms u1919
end Delivery.IrregularNine14.P10
