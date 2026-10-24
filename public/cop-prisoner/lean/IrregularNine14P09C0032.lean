import RowPrefixCornerWitness
import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P09C0001

namespace Delivery.IrregularNine14.P09
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b1920 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 426, targets := 1 },{ cop := 2, region := 440, targets := 64 }], pairs := [(1,0),(3,0),(3,6),(4,6)], upper := (rows 35 194 69 168 273 288 80 140 268), lower := (rows 35 194 69 168 273 288 80 128 256), losses := [] }

theorem u1920 : Upper (D 9) (R 9) [34,192,65,160,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1920 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1921 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8)], upper := (rows 35 194 69 168 276 48 65 392 264), lower := (rows 35 194 69 168 276 48 65 128 256), losses := [] }

theorem u1921 : Upper (D 9) (R 9) [34,192,65,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1921 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1922 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 309, targets := 128 }], pairs := [(0,7),(2,7),(4,7)], upper := (rows 35 194 69 168 276 48 72 385 257), lower := (rows 35 194 69 168 276 48 72 128 256), losses := [] }

theorem u1922 : Upper (D 9) (R 9) [34,192,65,160,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1922 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1923 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 440, targets := 64 },{ cop := 0, region := 136, targets := 256 }], pairs := [(0,8),(3,6),(3,8),(4,6)], upper := (rows 35 194 69 168 276 48 320 137 265), lower := (rows 35 194 69 168 276 48 320 128 256), losses := [{ target := 8, region := (rows 17 6 4 57 16 48 64 181 0), good := (rows 171 194 207 168 191 185 64 128 0) }] }

theorem u1923 : Upper (D 9) (R 9) [34,192,65,160,260,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1923 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1924 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 194 69 168 276 288 65 152 280), lower := (rows 35 194 69 168 276 288 65 128 256), losses := [] }

theorem u1924 : Upper (D 9) (R 9) [34,192,65,160,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1924 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1925 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 309, targets := 128 },{ cop := 3, region := 67, targets := 256 }], pairs := [(0,7),(0,8),(2,7),(4,7)], upper := (rows 35 194 69 168 276 288 72 145 273), lower := (rows 35 194 69 168 276 288 72 128 256), losses := [] }

theorem u1925 : Upper (D 9) (R 9) [34,192,65,160,260,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1925 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1926 : PairBound 9 := { available := 9, camps := [{ cop := 1, region := 297, targets := 64 },{ cop := 0, region := 136, targets := 256 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,6),(3,6),(3,8),(4,6)], upper := (rows 35 194 69 168 276 288 80 137 265), lower := (rows 35 194 69 168 276 288 80 128 256), losses := [] }

theorem u1926 : Upper (D 9) (R 9) [34,192,65,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1926 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1927 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8),(3,0)], upper := (rows 35 194 69 168 280 288 65 148 276), lower := (rows 35 194 69 168 280 288 65 128 256), losses := [] }

theorem u1927 : Upper (D 9) (R 9) [34,192,65,160,264,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1927 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1928 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 1, region := 313, targets := 64 }], pairs := [(0,6),(2,5),(2,7),(2,8)], upper := (rows 35 194 69 168 280 288 68 145 273), lower := (rows 35 194 69 168 280 288 68 128 256), losses := [] }

theorem u1928 : Upper (D 9) (R 9) [34,192,65,160,264,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1928 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1929 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 293, targets := 128 },{ cop := 2, region := 440, targets := 64 }], pairs := [(0,7),(2,7),(3,6),(4,6)], upper := (rows 35 194 69 168 280 288 80 133 261), lower := (rows 35 194 69 168 280 288 80 128 256), losses := [] }

theorem u1929 : Upper (D 9) (R 9) [34,192,65,160,264,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1929 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1930 : PairBound 9 := { available := 160, camps := [{ cop := 1, region := 297, targets := 64 },{ cop := 3, region := 84, targets := 32 }], pairs := [(0,6),(2,5),(3,6)], upper := (rows 35 194 69 265 276 40 80 160 416), lower := (rows 35 194 69 265 276 40 80 128 256), losses := [] }

theorem u1930 : Upper (D 9) (R 9) [34,192,65,257,260,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1930 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1931 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 194 69 265 276 40 96 144 400), lower := (rows 35 194 69 265 276 40 96 128 256), losses := [] }

theorem u1931 : Upper (D 9) (R 9) [34,192,65,257,260,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1931 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1932 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 69 265 276 40 192 176 304), lower := (rows 35 194 69 265 276 40 192 128 256), losses := [] }

theorem u1932 : Upper (D 9) (R 9) [34,192,65,257,260,8,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1932 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1933 : PairBound 9 := { available := 160, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 2, region := 440, targets := 64 }], pairs := [(1,0),(3,6),(4,0)], upper := (rows 35 194 69 265 276 48 72 160 416), lower := (rows 35 194 69 265 276 48 72 128 256), losses := [] }

theorem u1933 : Upper (D 9) (R 9) [34,192,65,257,260,16,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1933 [(5,4),(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1934 : PairBound 9 := { available := 136, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 194 69 265 276 48 96 136 392), lower := (rows 35 194 69 265 276 48 96 128 256), losses := [] }

theorem u1934 : Upper (D 9) (R 9) [34,192,65,257,260,16,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1934 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1935 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 317, targets := 128 }], pairs := [(0,7),(2,7),(3,7),(4,7)], upper := (rows 35 194 69 265 276 48 192 168 296), lower := (rows 35 194 69 265 276 48 192 128 256), losses := [] }

theorem u1935 : Upper (D 9) (R 9) [34,192,65,257,260,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1935 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1936 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 416 }], pairs := [(2,5),(2,7),(2,8)], upper := (rows 35 194 69 265 400 40 68 176 304), lower := (rows 35 194 69 265 400 40 68 128 256), losses := [] }

theorem u1936 : Upper (D 9) (R 9) [34,192,65,257,384,8,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1936 [(5,3),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1937 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 69 265 400 40 80 164 292), lower := (rows 35 194 69 265 400 40 80 128 256), losses := [] }

theorem u1937 : Upper (D 9) (R 9) [34,192,65,257,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1937 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1938 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 194 69 265 400 40 96 148 276), lower := (rows 35 194 69 265 400 40 96 128 256), losses := [] }

theorem u1938 : Upper (D 9) (R 9) [34,192,65,257,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1938 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1939 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 68, targets := 416 },{ cop := 2, region := 442, targets := 1 }], pairs := [(1,0),(2,5),(2,7),(2,8)], upper := (rows 35 194 69 268 400 40 65 176 304), lower := (rows 35 194 69 268 400 40 65 128 256), losses := [] }

theorem u1939 : Upper (D 9) (R 9) [34,192,65,260,384,8,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1939 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1940 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 69 268 400 40 80 161 289), lower := (rows 35 194 69 268 400 40 80 128 256), losses := [] }

theorem u1940 : Upper (D 9) (R 9) [34,192,65,260,384,8,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1940 [(5,3),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1941 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 },{ cop := 0, region := 68, targets := 128 }], pairs := [(1,5),(2,7),(3,5),(4,5)], upper := (rows 35 194 69 268 400 40 96 145 273), lower := (rows 35 194 69 268 400 40 96 128 256), losses := [] }

theorem u1941 : Upper (D 9) (R 9) [34,192,65,260,384,8,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1941 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1942 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 152 273 33 68 416 288), lower := (rows 35 194 76 152 273 33 68 128 256), losses := [] }

theorem u1942 : Upper (D 9) (R 9) [34,192,72,144,257,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1942 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1943 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 2, region := 386, targets := 33 }], pairs := [(0,8),(1,0),(1,5),(1,8),(2,8)], upper := (rows 35 194 76 152 273 33 96 388 260), lower := (rows 35 194 76 152 273 33 96 128 256), losses := [] }

theorem u1943 : Upper (D 9) (R 9) [34,192,72,144,257,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1943 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1944 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 76 152 273 33 320 164 292), lower := (rows 35 194 76 152 273 33 320 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 32 336 128 256), good := (rows 34 194 78 222 336 32 320 128 320) }] }

theorem u1944 : Upper (D 9) (R 9) [34,192,72,144,257,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1944 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1945 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(1,8),(2,8),(3,6)], upper := (rows 35 194 76 152 273 36 65 416 288), lower := (rows 35 194 76 152 273 36 65 128 256), losses := [] }

theorem u1945 : Upper (D 9) (R 9) [34,192,72,144,257,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1945 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1946 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 408, targets := 96 }], pairs := [(3,5),(3,6),(4,5),(4,6)], upper := (rows 35 194 76 152 273 36 96 385 257), lower := (rows 35 194 76 152 273 36 96 128 256), losses := [] }

theorem u1946 : Upper (D 9) (R 9) [34,192,72,144,257,4,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1946 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1947 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,8),(1,8),(3,6),(4,6)], upper := (rows 35 194 76 152 273 36 320 161 289), lower := (rows 35 194 76 152 273 36 320 128 256), losses := [] }

theorem u1947 : Upper (D 9) (R 9) [34,192,72,144,257,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1947 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1948 : PairBound 9 := { available := 36, camps := [{ cop := 2, region := 418, targets := 1 }], pairs := [(1,0),(1,5),(1,8),(2,5),(2,7)], upper := (rows 35 194 76 152 273 288 65 164 292), lower := (rows 35 194 76 152 273 288 65 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 16 0 81 128 256), good := (rows 67 194 78 222 337 256 65 128 256) },{ target := 7, region := (rows 1 2 12 8 16 316 81 0 268), good := (rows 99 66 364 380 369 288 65 0 288) },{ target := 8, region := (rows 1 10 12 8 16 32 81 128 0), good := (rows 99 194 78 222 81 32 65 128 0) }] }

theorem u1948 : Upper (D 9) (R 9) [34,192,72,144,257,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1948 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1949 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 289 }], pairs := [(1,0),(1,5),(1,8),(2,0)], upper := (rows 35 194 76 152 273 288 68 161 289), lower := (rows 35 194 76 152 273 288 68 128 256), losses := [] }

theorem u1949 : Upper (D 9) (R 9) [34,192,72,144,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1949 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1950 : PairBound 9 := { available := 5, camps := [], pairs := [(1,0),(1,8),(2,0),(2,7),(2,8)], upper := (rows 35 194 76 152 273 288 96 133 261), lower := (rows 35 194 76 152 273 288 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 304 377 128 256), good := (rows 98 194 78 254 368 352 96 128 352) },{ target := 7, region := (rows 1 2 12 8 16 304 377 0 256), good := (rows 99 66 76 124 369 352 96 0 352) },{ target := 8, region := (rows 1 18 20 24 16 32 97 144 0), good := (rows 99 194 76 158 223 96 96 128 0) }] }

theorem u1950 : Upper (D 9) (R 9) [34,192,72,144,257,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1950 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1951 : PairBound 9 := { available := 288, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 152 276 33 65 416 288), lower := (rows 35 194 76 152 276 33 65 128 256), losses := [] }

theorem u1951 : Upper (D 9) (R 9) [34,192,72,144,260,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1951 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1952 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(2,8)], upper := (rows 35 194 76 152 276 33 96 385 257), lower := (rows 35 194 76 152 276 33 96 128 256), losses := [] }

theorem u1952 : Upper (D 9) (R 9) [34,192,72,144,260,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1952 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1953 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 163, targets := 256 },{ cop := 1, region := 33, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 76 152 276 33 320 161 289), lower := (rows 35 194 76 152 276 33 320 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 32 336 128 256), good := (rows 34 194 78 222 340 32 320 128 320) }] }

theorem u1953 : Upper (D 9) (R 9) [34,192,72,144,260,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1953 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1954 : PairBound 9 := { available := 33, camps := [{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,8),(3,6)], upper := (rows 35 194 76 152 276 288 65 161 289), lower := (rows 35 194 76 152 276 288 65 128 256), losses := [{ target := 6, region := (rows 3 2 4 12 20 375 0 195 323), good := (rows 419 419 444 184 316 288 417 128 288) }] }

theorem u1954 : Upper (D 9) (R 9) [34,192,72,144,260,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1954 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1955 : PairBound 9 := { available := 1, camps := [{ cop := 5, region := 195, targets := 256 },{ cop := 1, region := 289, targets := 64 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 76 152 276 288 96 129 257), lower := (rows 35 194 76 152 276 288 96 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 304 377 128 256), good := (rows 98 194 78 254 372 352 96 128 352) }] }

theorem u1955 : Upper (D 9) (R 9) [34,192,72,144,260,256,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1955 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1956 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 2, region := 386, targets := 33 }], pairs := [(0,8),(1,0),(1,5),(1,8),(2,8)], upper := (rows 35 194 76 152 304 33 65 388 260), lower := (rows 35 194 76 152 304 33 65 128 256), losses := [] }

theorem u1956 : Upper (D 9) (R 9) [34,192,72,144,288,1,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1956 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1957 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 152 304 33 68 385 257), lower := (rows 35 194 76 152 304 33 68 128 256), losses := [] }

theorem u1957 : Upper (D 9) (R 9) [34,192,72,144,288,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1957 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1958 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 33, targets := 448 },{ cop := 2, region := 163, targets := 256 }], pairs := [(0,6),(0,7),(0,8),(1,0),(1,8)], upper := (rows 35 194 76 152 304 33 320 133 261), lower := (rows 35 194 76 152 304 33 320 128 256), losses := [{ target := 0, region := (rows 0 10 12 8 16 32 336 128 256), good := (rows 34 194 78 222 368 32 320 128 320) }] }

theorem u1958 : Upper (D 9) (R 9) [34,192,72,144,288,1,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1958 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1959 : PairBound 9 := { available := 260, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 2, region := 386, targets := 1 }], pairs := [(0,8),(1,0),(1,8),(2,8)], upper := (rows 35 194 76 168 273 48 65 388 260), lower := (rows 35 194 76 168 273 48 65 128 256), losses := [] }

theorem u1959 : Upper (D 9) (R 9) [34,192,72,160,257,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1959 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1960 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0)], upper := (rows 35 194 76 168 273 48 68 385 257), lower := (rows 35 194 76 168 273 48 68 128 256), losses := [] }

theorem u1960 : Upper (D 9) (R 9) [34,192,72,160,257,16,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1960 [(5,4),(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1961 : Route 9 := (fun mask => (mask,id))

def c1961 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1961 : Upper (D 9) (R 9) [34,192,72,160,257,16,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,16,256] 13 (by decide) (choices 1) [1,4] r1961 c1961
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u103
  · exact u104

def r1962 : Route 9 := (fun mask => (mask,id))

def c1962 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1962 : Upper (D 9) (R 9) [34,192,72,160,257,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,256,1] 13 (by decide) (choices 1) [4,16] r1962 c1962
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u105
  · exact u106

def b1963 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 70, targets := 33 }], pairs := [(1,0),(1,5),(2,0),(2,5)], upper := (rows 35 194 76 168 273 288 68 145 273), lower := (rows 35 194 76 168 273 288 68 128 256), losses := [] }

theorem u1963 : Upper (D 9) (R 9) [34,192,72,160,257,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1963 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1964 : Route 9 := (fun mask => (mask,id))

def c1964 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1964 : Upper (D 9) (R 9) [34,192,72,160,257,256,16] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,257,256,16] 13 (by decide) (choices 1) [1,4] r1964 c1964
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u107
  · exact u108

def b1965 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 71, targets := 256 },{ cop := 0, region := 450, targets := 32 }], pairs := [(0,8),(1,5),(1,8),(2,8)], upper := (rows 35 194 76 168 276 48 65 385 257), lower := (rows 35 194 76 168 276 48 65 128 256), losses := [] }

theorem u1965 : Upper (D 9) (R 9) [34,192,72,160,260,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1965 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def r1966 : Route 9 := (fun mask => (mask,id))

def c1966 : Nat → Fin 9 := (fun _ => 0)

theorem u1966 : Upper (D 9) (R 9) [34,192,72,160,260,16,256] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,16,256] 13 (by decide) (choices 1) [1] r1966 c1966
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl
  · exact u109

def r1967 : Route 9 := (fun mask => (mask,id))

def c1967 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 32 => 5 | 64 => 6 | 256 => 8 | _ => 0)

theorem u1967 : Upper (D 9) (R 9) [34,192,72,160,260,256,1] 13 := by
  apply FastRouting.sound _ _ [34,192,72,160,260,256,1] 13 (by decide) (choices 1) [1,16] r1967 c1967
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u110
  · exact u111

def b1968 : PairBound 9 := { available := 1, camps := [{ cop := 1, region := 297, targets := 64 },{ cop := 0, region := 136, targets := 256 },{ cop := 1, region := 289, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(3,8)], upper := (rows 35 194 76 168 276 288 80 129 257), lower := (rows 35 194 76 168 276 288 80 128 256), losses := [] }

theorem u1968 : Upper (D 9) (R 9) [34,192,72,160,260,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1968 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1969 : PairBound 9 := { available := 272, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 35 194 76 265 176 36 65 400 272), lower := (rows 35 194 76 265 176 36 65 128 256), losses := [] }

theorem u1969 : Upper (D 9) (R 9) [34,192,72,257,160,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1969 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1970 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 76 265 176 36 80 385 257), lower := (rows 35 194 76 265 176 36 80 128 256), losses := [] }

theorem u1970 : Upper (D 9) (R 9) [34,192,72,257,160,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1970 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1971 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 179, targets := 256 },{ cop := 0, region := 408, targets := 64 }], pairs := [(0,8),(1,8),(3,6),(4,8)], upper := (rows 35 194 76 265 176 36 320 145 273), lower := (rows 35 194 76 265 176 36 320 128 256), losses := [] }

theorem u1971 : Upper (D 9) (R 9) [34,192,72,257,160,4,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1971 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1972 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 434, targets := 1 },{ cop := 3, region := 68, targets := 288 },{ cop := 4, region := 67, targets := 256 }], pairs := [(0,8),(1,0),(2,5),(2,8),(4,0)], upper := (rows 35 194 76 265 176 288 65 148 276), lower := (rows 35 194 76 265 176 288 65 128 256), losses := [] }

theorem u1972 : Upper (D 9) (R 9) [34,192,72,257,160,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1972 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1973 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 313, targets := 64 },{ cop := 3, region := 68, targets := 1 }], pairs := [(0,6),(2,0),(3,6),(4,6)], upper := (rows 35 194 76 265 176 288 68 145 273), lower := (rows 35 194 76 265 176 288 68 128 256), losses := [] }

theorem u1973 : Upper (D 9) (R 9) [34,192,72,257,160,256,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1973 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1974 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 4, region := 66, targets := 1 }], pairs := [(0,7),(1,0),(2,7),(3,7)], upper := (rows 35 194 76 265 176 288 80 133 261), lower := (rows 35 194 76 265 176 288 80 128 256), losses := [] }

theorem u1974 : Upper (D 9) (R 9) [34,192,72,257,160,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1974 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1975 : PairBound 9 := { available := 48, camps := [{ cop := 1, region := 313, targets := 64 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,6),(0,7),(3,6),(4,6)], upper := (rows 35 194 76 265 400 33 68 176 304), lower := (rows 35 194 76 265 400 33 68 128 256), losses := [] }

theorem u1975 : Upper (D 9) (R 9) [34,192,72,257,384,1,4] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1975 [(6,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1976 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 301, targets := 128 },{ cop := 1, region := 33, targets := 64 }], pairs := [(0,6),(0,7),(2,7),(3,7)], upper := (rows 35 194 76 265 400 33 80 164 292), lower := (rows 35 194 76 265 400 33 80 128 256), losses := [] }

theorem u1976 : Upper (D 9) (R 9) [34,192,72,257,384,1,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1976 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1977 : PairBound 9 := { available := 20, camps := [{ cop := 2, region := 402, targets := 33 },{ cop := 1, region := 33, targets := 128 }], pairs := [(0,7),(1,0),(1,5),(4,0),(4,5)], upper := (rows 35 194 76 265 400 33 96 148 276), lower := (rows 35 194 76 265 400 33 96 128 256), losses := [] }

theorem u1977 : Upper (D 9) (R 9) [34,192,72,257,384,1,32] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1977 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1978 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 408, targets := 64 },{ cop := 2, region := 434, targets := 1 }], pairs := [(1,0),(3,6),(4,0),(4,6)], upper := (rows 35 194 76 265 400 36 65 176 304), lower := (rows 35 194 76 265 400 36 65 128 256), losses := [] }

theorem u1978 : Upper (D 9) (R 9) [34,192,72,257,384,4,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1978 [(5,2)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b1979 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 301, targets := 128 }], pairs := [(0,7),(2,7),(3,7)], upper := (rows 35 194 76 265 400 36 80 161 289), lower := (rows 35 194 76 265 400 36 80 128 256), losses := [] }

theorem u1979 : Upper (D 9) (R 9) [34,192,72,257,384,4,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b1979 [(5,2),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u1979
end Delivery.IrregularNine14.P09
