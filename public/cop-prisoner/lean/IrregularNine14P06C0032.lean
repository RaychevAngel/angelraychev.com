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

def b1920 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 19 164 76 336 33 68 162 290), lower := (rows 11 19 164 76 336 33 68 128 256), losses := [] }

theorem u1920 : Upper (D 6) (R 6) [10,17,160,68,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1920
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 164 76 336 33 96 134 262), lower := (rows 11 19 164 76 336 33 96 128 256), losses := [] }

theorem u1921 : Upper (D 6) (R 6) [10,17,160,68,320,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1921
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 132, targets := 67 }], pairs := [(2,0),(2,1),(2,6)], upper := (rows 11 19 164 76 336 34 65 164 292), lower := (rows 11 19 164 76 336 34 65 128 256), losses := [] }

theorem u1922 : Upper (D 6) (R 6) [10,17,160,68,320,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1922
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 72, targets := 35 }], pairs := [(3,0),(3,1),(3,5)], upper := (rows 11 19 164 76 336 34 68 161 289), lower := (rows 11 19 164 76 336 34 68 128 256), losses := [] }

theorem u1923 : Upper (D 6) (R 6) [10,17,160,68,320,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1923
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 275, targets := 32 }], pairs := [(0,5),(1,5),(4,5)], upper := (rows 11 19 164 76 336 34 96 133 261), lower := (rows 11 19 164 76 336 34 96 128 256), losses := [] }

theorem u1924 : Upper (D 6) (R 6) [10,17,160,68,320,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1924
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 104 276 33 66 196 324), lower := (rows 11 19 164 104 276 33 66 128 256), losses := [] }

theorem u1925 : Upper (D 6) (R 6) [10,17,160,96,260,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1925
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,0),(3,0),(3,1)], upper := (rows 11 19 164 104 276 33 68 194 322), lower := (rows 11 19 164 104 276 33 68 128 256), losses := [{ target := 0, region := (rows 0 2 36 44 48 32 124 131 259), good := (rows 458 466 252 124 348 508 76 128 256) }] }

theorem u1926 : Upper (D 6) (R 6) [10,17,160,96,260,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1926
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 404, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 164 104 276 34 65 196 324), lower := (rows 11 19 164 104 276 34 65 128 256), losses := [] }

theorem u1927 : Upper (D 6) (R 6) [10,17,160,96,260,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1927
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(2,1),(3,0),(3,1)], upper := (rows 11 19 164 104 276 34 68 193 321), lower := (rows 11 19 164 104 276 34 68 128 256), losses := [{ target := 1, region := (rows 1 0 36 44 48 32 124 131 259), good := (rows 457 465 252 124 348 508 76 128 256) }] }

theorem u1928 : Upper (D 6) (R 6) [10,17,160,96,260,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1928
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 96, camps := [{ cop := 5, region := 468, targets := 3 }], pairs := [(2,0),(2,1),(4,0)], upper := (rows 11 19 388 13 112 34 68 224 352), lower := (rows 11 19 388 13 112 34 68 128 256), losses := [] }

theorem u1929 : Upper (D 6) (R 6) [10,17,384,5,96,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1929
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 399, targets := 32 }], pairs := [(0,5),(1,5),(2,5)], upper := (rows 11 19 388 13 112 36 96 194 322), lower := (rows 11 19 388 13 112 36 96 128 256), losses := [] }

theorem u1930 : Upper (D 6) (R 6) [10,17,384,5,96,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1930
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 66, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 388 44 84 33 96 194 322), lower := (rows 11 19 388 44 84 33 96 128 256), losses := [] }

theorem u1931 : Upper (D 6) (R 6) [10,17,384,36,68,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1931
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 43, targets := 64 }], pairs := [(0,6),(1,6),(3,6)], upper := (rows 11 19 388 44 84 34 96 193 321), lower := (rows 11 19 388 44 84 34 96 128 256), losses := [] }

theorem u1932 : Upper (D 6) (R 6) [10,17,384,36,68,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1932
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 120, targets := 3 }], pairs := [(3,0),(3,1),(4,0)], upper := (rows 11 19 388 44 84 96 96 131 259), lower := (rows 11 19 388 44 84 96 96 128 256), losses := [] }

theorem u1933 : Upper (D 6) (R 6) [10,17,384,36,68,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1933
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 2, region := 136, targets := 2 }], pairs := [(1,0),(3,1),(4,0)], upper := (rows 11 22 37 137 336 96 66 164 292), lower := (rows 11 22 37 137 336 96 66 128 256), losses := [] }

theorem u1934 : Upper (D 6) (R 6) [10,20,33,129,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1934
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 338, targets := 1 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,0),(2,1),(4,0)], upper := (rows 11 22 37 137 336 96 68 162 290), lower := (rows 11 22 37 137 336 96 68 128 256), losses := [] }

theorem u1935 : Upper (D 6) (R 6) [10,20,33,129,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1935
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 37 137 336 96 96 134 262), lower := (rows 11 22 37 137 336 96 96 128 256), losses := [] }

theorem u1936 : Upper (D 6) (R 6) [10,20,33,129,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1936
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 232, targets := 1 }], pairs := [(3,0),(3,1),(4,2)], upper := (rows 11 22 37 140 273 96 66 224 352), lower := (rows 11 22 37 140 273 96 66 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 96 64 224 352), good := (rows 9 28 445 156 273 480 480 128 256) }] }

theorem u1937 : Upper (D 6) (R 6) [10,20,33,132,257,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1937
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 368, targets := 4 },{ cop := 1, region := 232, targets := 1 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 22 37 140 273 96 96 194 322), lower := (rows 11 22 37 140 273 96 96 128 256), losses := [] }

theorem u1938 : Upper (D 6) (R 6) [10,20,33,132,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1938
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 100, targets := 2 },{ cop := 0, region := 368, targets := 4 }], pairs := [(2,1),(3,0),(4,2)], upper := (rows 11 22 37 140 336 96 65 162 290), lower := (rows 11 22 37 140 336 96 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 16 112 64 130 258), good := (rows 394 446 36 140 368 96 96 128 256) }] }

theorem u1939 : Upper (D 6) (R 6) [10,20,33,132,320,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1939
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 136, targets := 66 },{ cop := 0, region := 368, targets := 4 }], pairs := [(3,1),(3,6),(4,2)], upper := (rows 11 22 37 140 336 96 66 161 289), lower := (rows 11 22 37 140 336 96 66 128 256), losses := [] }

theorem u1940 : Upper (D 6) (R 6) [10,20,33,132,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1940
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 137, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 37 140 336 96 96 131 259), lower := (rows 11 22 37 140 336 96 96 128 256), losses := [] }

theorem u1941 : Upper (D 6) (R 6) [10,20,33,132,320,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1941
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 6, camps := [{ cop := 2, region := 338, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 22 37 168 336 96 65 134 262), lower := (rows 11 22 37 168 336 96 65 128 256), losses := [] }

theorem u1942 : Upper (D 6) (R 6) [10,20,33,160,320,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1942
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 136, targets := 66 },{ cop := 2, region := 338, targets := 32 }], pairs := [(1,5),(3,1),(3,6)], upper := (rows 11 22 37 168 336 96 66 133 261), lower := (rows 11 22 37 168 336 96 66 128 256), losses := [] }

theorem u1943 : Upper (D 6) (R 6) [10,20,33,160,320,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1943
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 338, targets := 32 },{ cop := 0, region := 100, targets := 2 }], pairs := [(1,5),(2,1),(4,5)], upper := (rows 11 22 37 168 336 96 68 131 259), lower := (rows 11 22 37 168 336 96 68 128 256), losses := [] }

theorem u1944 : Upper (D 6) (R 6) [10,20,33,160,320,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1944
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,1),(2,6),(3,0)], upper := (rows 11 22 37 200 336 36 65 162 290), lower := (rows 11 22 37 200 336 36 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 72 80 38 64 131 259), good := (rows 426 438 420 216 344 36 472 128 256) }] }

theorem u1945 : Upper (D 6) (R 6) [10,20,33,192,320,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1945
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 36, targets := 66 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 22 37 200 336 36 66 161 289), lower := (rows 11 22 37 200 336 36 66 128 256), losses := [{ target := 2, region := (rows 67 2 0 14 22 32 67 132 260), good := (rows 91 475 505 201 337 440 91 128 256) }] }

theorem u1946 : Upper (D 6) (R 6) [10,20,33,192,320,4,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1946
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 36, targets := 2 },{ cop := 0, region := 36, targets := 64 }], pairs := [(0,2),(2,1),(2,6)], upper := (rows 11 22 37 200 336 36 96 131 259), lower := (rows 11 22 37 200 336 36 96 128 256), losses := [{ target := 2, region := (rows 3 2 0 14 22 32 100 131 259), good := (rows 411 475 505 200 336 120 96 128 256) }] }

theorem u1947 : Upper (D 6) (R 6) [10,20,33,192,320,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1947
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 392, targets := 67 }], pairs := [(3,0),(3,1),(3,6)], upper := (rows 11 22 37 392 81 96 66 164 292), lower := (rows 11 22 37 392 81 96 66 128 256), losses := [] }

theorem u1948 : Upper (D 6) (R 6) [10,20,33,384,65,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1948
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 116, targets := 2 },{ cop := 2, region := 82, targets := 32 }], pairs := [(1,5),(2,1),(4,1)], upper := (rows 11 22 37 392 81 96 68 162 290), lower := (rows 11 22 37 392 81 96 68 128 256), losses := [] }

theorem u1949 : Upper (D 6) (R 6) [10,20,33,384,65,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1949
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 393, targets := 96 }], pairs := [(0,5),(0,6),(3,5)], upper := (rows 11 22 37 392 81 96 96 134 262), lower := (rows 11 22 37 392 81 96 96 128 256), losses := [] }

theorem u1950 : Upper (D 6) (R 6) [10,20,33,384,65,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1950
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 73, targets := 36 }], pairs := [(0,2),(0,5)], upper := (rows 11 22 38 73 208 288 65 164 292), lower := (rows 11 22 38 73 208 288 65 128 256), losses := [] }

theorem u1951 : Upper (D 6) (R 6) [10,20,34,65,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1951
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 }], pairs := [(0,5),(3,5)], upper := (rows 11 22 38 73 208 288 68 161 289), lower := (rows 11 22 38 73 208 288 68 128 256), losses := [] }

theorem u1952 : Upper (D 6) (R 6) [10,20,34,65,192,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1952
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 22 38 73 208 288 96 133 261), lower := (rows 11 22 38 73 208 288 96 128 256), losses := [] }

theorem u1953 : Upper (D 6) (R 6) [10,20,34,65,192,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1953
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 36, camps := [{ cop := 5, region := 406, targets := 65 }], pairs := [(1,0),(1,6),(2,0)], upper := (rows 11 22 38 73 400 96 65 164 292), lower := (rows 11 22 38 73 400 96 65 128 256), losses := [] }

theorem u1954 : Upper (D 6) (R 6) [10,20,34,65,384,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1954
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 73, targets := 32 },{ cop := 3, region := 432, targets := 2 }], pairs := [(0,5),(3,5),(4,1)], upper := (rows 11 22 38 73 400 96 68 161 289), lower := (rows 11 22 38 73 400 96 68 128 256), losses := [] }

theorem u1955 : Upper (D 6) (R 6) [10,20,34,65,384,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1955
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 104, targets := 6 },{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(3,1),(3,2)], upper := (rows 11 22 38 73 400 96 96 133 261), lower := (rows 11 22 38 73 400 96 96 128 256), losses := [] }

theorem u1956 : Upper (D 6) (R 6) [10,20,34,65,384,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1956
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 68, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 22 38 104 145 288 65 196 324), lower := (rows 11 22 38 104 145 288 65 128 256), losses := [] }

theorem u1957 : Upper (D 6) (R 6) [10,20,34,96,129,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1957
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 22 38 104 145 288 68 193 321), lower := (rows 11 22 38 104 145 288 68 128 256), losses := [] }

theorem u1958 : Upper (D 6) (R 6) [10,20,34,96,129,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1958
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 104 208 33 65 388 260), lower := (rows 11 22 38 104 208 33 65 128 256), losses := [] }

theorem u1959 : Upper (D 6) (R 6) [10,20,34,96,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1959
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 257, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 22 38 104 208 33 68 385 257), lower := (rows 11 22 38 104 208 33 68 128 256), losses := [] }

theorem u1960 : Upper (D 6) (R 6) [10,20,34,96,192,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1960
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1961 : Route 9 := (fun mask => (mask,id))

def c1961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1961 : Upper (D 6) (R 6) [10,20,34,96,192,1,256] 13 := by
  apply FastRouting.sound _ _ [10,20,34,96,192,1,256] 13 (by decide) (choices 1) [1,4] r1961 c1961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u108
  · exact u109

def b1962 : PairBound 9 := { available := 5, camps := [{ cop := 2, region := 73, targets := 4 }], pairs := [(0,2),(3,2)], upper := (rows 11 22 38 104 208 288 65 133 261), lower := (rows 11 22 38 104 208 288 65 128 256), losses := [] }

theorem u1962 : Upper (D 6) (R 6) [10,20,34,96,192,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1962
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1963 : PairBound 9 := { available := 1, camps := [{ cop := 2, region := 72, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 11 22 38 104 208 288 68 129 257), lower := (rows 11 22 38 104 208 288 68 128 256), losses := [] }

theorem u1963 : Upper (D 6) (R 6) [10,20,34,96,192,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1963
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1964 : PairBound 9 := { available := 68, camps := [{ cop := 3, region := 406, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 38 104 400 33 65 196 324), lower := (rows 11 22 38 104 400 33 65 128 256), losses := [] }

theorem u1964 : Upper (D 6) (R 6) [10,20,34,96,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1964
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1965 : PairBound 9 := { available := 65, camps := [{ cop := 2, region := 72, targets := 3 },{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,0),(3,1)], upper := (rows 11 22 38 104 400 33 68 193 321), lower := (rows 11 22 38 104 400 33 68 128 256), losses := [] }

theorem u1965 : Upper (D 6) (R 6) [10,20,34,96,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1965
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1966 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 80, targets := 6 }], pairs := [(4,1),(4,2)], upper := (rows 11 22 38 168 81 288 65 196 324), lower := (rows 11 22 38 168 81 288 65 128 256), losses := [] }

theorem u1966 : Upper (D 6) (R 6) [10,20,34,160,65,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1966
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1967 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 424, targets := 6 }], pairs := [(3,1),(3,2)], upper := (rows 11 22 38 168 81 288 68 193 321), lower := (rows 11 22 38 168 81 288 68 128 256), losses := [] }

theorem u1967 : Upper (D 6) (R 6) [10,20,34,160,65,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1967
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1968 : PairBound 9 := { available := 68, camps := [], pairs := [(3,1),(4,1),(4,5)], upper := (rows 11 22 38 168 273 96 65 196 324), lower := (rows 11 22 38 168 273 96 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 15 17 115 81 130 258), good := (rows 505 508 428 168 377 96 121 128 256) },{ target := 5, region := (rows 1 2 4 8 17 0 81 130 258), good := (rows 475 470 390 136 337 64 81 128 256) }] }

theorem u1968 : Upper (D 6) (R 6) [10,20,34,160,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1968
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 65, camps := [{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 38 168 273 96 68 193 321), lower := (rows 11 22 38 168 273 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 25 17 103 70 129 257), good := (rows 505 124 100 168 441 96 100 128 256) }] }

theorem u1969 : Upper (D 6) (R 6) [10,20,34,160,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1969
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 22 38 168 336 33 65 196 324), lower := (rows 11 22 38 168 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 97 97 132 260), good := (rows 105 412 508 232 368 97 97 128 256) }] }

theorem u1970 : Upper (D 6) (R 6) [10,20,34,160,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1970
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 22 38 168 336 33 68 193 321), lower := (rows 11 22 38 168 336 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 41 17 33 70 129 257), good := (rows 505 84 108 168 336 441 68 128 256) }] }

theorem u1971 : Upper (D 6) (R 6) [10,20,34,160,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1971
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 36, camps := [], pairs := [(1,0),(2,0),(3,0)], upper := (rows 11 22 38 200 273 96 65 164 292), lower := (rows 11 22 38 200 273 96 65 128 256), losses := [{ target := 0, region := (rows 0 18 5 104 16 104 64 197 325), good := (rows 430 406 430 488 406 488 492 128 256) }] }

theorem u1972 : Upper (D 6) (R 6) [10,20,34,192,257,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1972
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 102, targets := 1 }], pairs := [(1,0),(2,0),(3,1)], upper := (rows 11 22 38 200 273 96 68 161 289), lower := (rows 11 22 38 200 273 96 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 11 17 111 70 145 273), good := (rows 505 508 108 232 441 96 100 128 256) }] }

theorem u1973 : Upper (D 6) (R 6) [10,20,34,192,257,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1973
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 5, camps := [{ cop := 7, region := 104, targets := 7 }], pairs := [(3,0),(3,1),(3,2)], upper := (rows 11 22 38 200 273 96 96 133 261), lower := (rows 11 22 38 200 273 96 96 128 256), losses := [] }

theorem u1974 : Upper (D 6) (R 6) [10,20,34,192,257,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1974
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 22 38 200 336 33 65 164 292), lower := (rows 11 22 38 200 336 33 65 128 256), losses := [{ target := 1, region := (rows 1 0 4 12 20 97 97 132 260), good := (rows 105 412 508 232 368 97 97 128 256) }] }

theorem u1975 : Upper (D 6) (R 6) [10,20,34,192,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1975
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 36, targets := 64 }], pairs := [(2,6),(3,1),(4,1)], upper := (rows 11 22 38 200 336 33 68 161 289), lower := (rows 11 22 38 200 336 33 68 128 256), losses := [{ target := 1, region := (rows 1 0 4 13 21 33 70 161 289), good := (rows 505 92 508 200 336 441 92 128 256) }] }

theorem u1976 : Upper (D 6) (R 6) [10,20,34,192,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1976
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r1977 : Route 9 := (fun mask => (mask,id))

def c1977 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1977 : Upper (D 6) (R 6) [10,20,34,192,320,1,32] 13 := by
  apply FastRouting.sound _ _ [10,20,34,192,320,1,32] 13 (by decide) (choices 1) [1,4] r1977 c1977
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u110
  · exact u111

def b1978 : PairBound 9 := { available := 68, camps := [{ cop := 6, region := 310, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 100 137 304 34 65 196 324), lower := (rows 11 22 100 137 304 34 65 128 256), losses := [] }

theorem u1978 : Upper (D 6) (R 6) [10,20,96,129,288,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1978
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 65, camps := [{ cop := 8, region := 118, targets := 1 }], pairs := [(1,0),(2,0),(4,0)], upper := (rows 11 22 100 137 304 34 68 193 321), lower := (rows 11 22 100 137 304 34 68 128 256), losses := [] }

theorem u1979 : Upper (D 6) (R 6) [10,20,96,129,288,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b1979
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P06
