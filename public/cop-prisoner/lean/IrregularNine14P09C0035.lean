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

def b2100 : PairBound 9 := { available := 258, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 7 44 137 208 288 80 386 258), lower := (rows 97 7 44 137 208 288 80 128 256), losses := [] }

theorem u2100 : Upper (D 9) (R 9) [96,5,40,129,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2100 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2101 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 137 208 288 320 146 274), lower := (rows 97 7 44 137 208 288 320 128 256), losses := [] }

theorem u2101 : Upper (D 9) (R 9) [96,5,40,129,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2101 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2102 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 }], pairs := [(1,7),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 137 274 48 192 448 320), lower := (rows 97 7 44 137 274 48 192 128 256), losses := [{ target := 7, region := (rows 1 10 12 8 26 62 64 0 321), good := (rows 353 311 62 319 306 48 320 0 256) }] }

theorem u2102 : Upper (D 9) (R 9) [96,5,40,129,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2102 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2103 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 137 274 48 320 192 448), lower := (rows 97 7 44 137 274 48 320 128 256), losses := [] }

theorem u2103 : Upper (D 9) (R 9) [96,5,40,129,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2103 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2104 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 137 274 288 80 192 448), lower := (rows 97 7 44 137 274 288 80 128 256), losses := [] }

theorem u2104 : Upper (D 9) (R 9) [96,5,40,129,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2104 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2105 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 }], pairs := [(0,8),(1,8),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 137 274 288 192 208 336), lower := (rows 97 7 44 137 274 288 192 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 32 216 144 0), good := (rows 97 7 111 201 210 32 192 192 0) }] }

theorem u2105 : Upper (D 9) (R 9) [96,5,40,129,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2105 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2106 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 137 336 288 66 144 400), lower := (rows 97 7 44 137 336 288 66 128 256), losses := [] }

theorem u2106 : Upper (D 9) (R 9) [96,5,40,129,320,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2106 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2107 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 44 137 336 288 80 130 386), lower := (rows 97 7 44 137 336 288 80 128 256), losses := [] }

theorem u2107 : Upper (D 9) (R 9) [96,5,40,129,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2107 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2108 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 1, region := 464, targets := 1 },{ cop := 4, region := 33, targets := 128 }], pairs := [(0,7),(0,8),(3,5),(4,0),(4,5)], upper := (rows 97 7 44 137 336 288 192 146 274), lower := (rows 97 7 44 137 336 288 192 128 256), losses := [{ target := 8, region := (rows 5 6 4 8 16 32 200 128 0), good := (rows 97 7 111 201 80 32 192 192 0) }] }

theorem u2108 : Upper (D 9) (R 9) [96,5,40,129,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2108 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2109 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 137 400 288 66 208 336), lower := (rows 97 7 44 137 400 288 66 128 256), losses := [] }

theorem u2109 : Upper (D 9) (R 9) [96,5,40,129,384,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2109 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2110 : PairBound 9 := { available := 66, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 137 400 288 80 194 322), lower := (rows 97 7 44 137 400 288 80 128 256), losses := [] }

theorem u2110 : Upper (D 9) (R 9) [96,5,40,129,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2110 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2111 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 353, targets := 128 }], pairs := [(0,7),(2,0),(3,5),(4,5)], upper := (rows 97 7 44 138 145 288 80 448 320), lower := (rows 97 7 44 138 145 288 80 128 256), losses := [{ target := 0, region := (rows 0 2 14 10 16 371 80 209 337), good := (rows 480 430 44 174 496 288 496 128 288) }] }

theorem u2111 : Upper (D 9) (R 9) [96,5,40,130,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2111 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2112 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 138 145 288 320 208 336), lower := (rows 97 7 44 138 145 288 320 128 256), losses := [] }

theorem u2112 : Upper (D 9) (R 9) [96,5,40,130,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2112 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2113 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 44 138 208 288 65 400 272), lower := (rows 97 7 44 138 208 288 65 128 256), losses := [] }

theorem u2113 : Upper (D 9) (R 9) [96,5,40,130,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2113 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2114 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 398, targets := 64 },{ cop := 3, region := 80, targets := 1 }], pairs := [(1,6),(2,6),(3,6),(4,0)], upper := (rows 97 7 44 138 208 288 80 385 257), lower := (rows 97 7 44 138 208 288 80 128 256), losses := [] }

theorem u2114 : Upper (D 9) (R 9) [96,5,40,130,192,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2114 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2115 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 138 208 288 320 145 273), lower := (rows 97 7 44 138 208 288 320 128 256), losses := [] }

theorem u2115 : Upper (D 9) (R 9) [96,5,40,130,192,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2115 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2116 : PairBound 9 := { available := 320, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(3,5),(4,5),(4,7)], upper := (rows 97 7 44 138 273 48 192 448 320), lower := (rows 97 7 44 138 273 48 192 128 256), losses := [] }

theorem u2116 : Upper (D 9) (R 9) [96,5,40,130,257,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2116 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2117 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 138 273 48 320 192 448), lower := (rows 97 7 44 138 273 48 320 128 256), losses := [] }

theorem u2117 : Upper (D 9) (R 9) [96,5,40,130,257,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2117 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2118 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 138 273 288 80 192 448), lower := (rows 97 7 44 138 273 288 80 128 256), losses := [] }

theorem u2118 : Upper (D 9) (R 9) [96,5,40,130,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2118 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2119 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 7 44 138 273 288 192 208 336), lower := (rows 97 7 44 138 273 288 192 128 256), losses := [{ target := 7, region := (rows 65 2 12 8 83 371 64 0 321), good := (rows 369 311 44 62 305 288 369 0 288) }] }

theorem u2119 : Upper (D 9) (R 9) [96,5,40,130,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2119 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2120 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 44 138 336 288 65 144 400), lower := (rows 97 7 44 138 336 288 65 128 256), losses := [] }

theorem u2120 : Upper (D 9) (R 9) [96,5,40,130,320,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2120 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2121 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 64 },{ cop := 0, region := 142, targets := 256 }], pairs := [(1,6),(1,8),(2,6),(3,6)], upper := (rows 97 7 44 138 336 288 80 129 385), lower := (rows 97 7 44 138 336 288 80 128 256), losses := [] }

theorem u2121 : Upper (D 9) (R 9) [96,5,40,130,320,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2121 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2122 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 6, region := 305, targets := 128 }], pairs := [(0,7),(2,7),(3,5),(4,5),(4,7)], upper := (rows 97 7 44 138 336 288 192 145 273), lower := (rows 97 7 44 138 336 288 192 128 256), losses := [{ target := 7, region := (rows 81 2 12 8 81 379 64 0 339), good := (rows 369 311 44 302 369 288 369 0 288) }] }

theorem u2122 : Upper (D 9) (R 9) [96,5,40,130,320,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2122 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2123 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 472, targets := 32 }], pairs := [(0,7),(0,8),(1,7),(1,8),(3,5)], upper := (rows 97 7 44 138 400 288 65 208 336), lower := (rows 97 7 44 138 400 288 65 128 256), losses := [] }

theorem u2123 : Upper (D 9) (R 9) [96,5,40,130,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2123 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2124 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 138 400 288 80 193 321), lower := (rows 97 7 44 138 400 288 80 128 256), losses := [] }

theorem u2124 : Upper (D 9) (R 9) [96,5,40,130,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2124 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2125 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 83, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,7)], upper := (rows 97 7 44 152 82 288 65 384 384), lower := (rows 97 7 44 152 82 288 65 128 256), losses := [] }

theorem u2125 : Upper (D 9) (R 9) [96,5,40,144,66,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2125 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2126 : PairBound 9 := { available := 257, camps := [{ cop := 1, region := 472, targets := 32 },{ cop := 4, region := 289, targets := 128 }], pairs := [(0,7),(2,6),(3,5),(3,6),(4,5)], upper := (rows 97 7 44 152 82 288 192 385 257), lower := (rows 97 7 44 152 82 288 192 128 256), losses := [{ target := 6, region := (rows 1 2 28 24 16 307 0 131 259), good := (rows 417 423 44 188 446 288 128 128 288) }] }

theorem u2126 : Upper (D 9) (R 9) [96,5,40,144,66,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2126 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2127 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 152 82 288 320 129 385), lower := (rows 97 7 44 152 82 288 320 128 256), losses := [] }

theorem u2127 : Upper (D 9) (R 9) [96,5,40,144,66,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2127 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2128 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 44 152 273 34 192 448 320), lower := (rows 97 7 44 152 273 34 192 128 256), losses := [] }

theorem u2128 : Upper (D 9) (R 9) [96,5,40,144,257,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2128 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2129 : PairBound 9 := { available := 192, camps := [{ cop := 0, region := 408, targets := 32 },{ cop := 4, region := 200, targets := 1 }], pairs := [(0,7),(3,0),(3,5),(4,5)], upper := (rows 97 7 44 152 273 34 320 192 448), lower := (rows 97 7 44 152 273 34 320 128 256), losses := [{ target := 7, region := (rows 9 14 12 8 16 46 336 0 256), good := (rows 97 39 47 127 337 34 320 0 320) }] }

theorem u2129 : Upper (D 9) (R 9) [96,5,40,144,257,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2129 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2130 : PairBound 9 := { available := 384, camps := [{ cop := 3, region := 103, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 152 336 34 65 384 384), lower := (rows 97 7 44 152 336 34 65 128 256), losses := [] }

theorem u2130 : Upper (D 9) (R 9) [96,5,40,144,320,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2130 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2131 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 103, targets := 256 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,8),(1,8),(2,8),(3,5)], upper := (rows 97 7 44 152 336 34 192 385 257), lower := (rows 97 7 44 152 336 34 192 128 256), losses := [] }

theorem u2131 : Upper (D 9) (R 9) [96,5,40,144,320,2,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2131 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2132 : PairBound 9 := { available := 129, camps := [{ cop := 4, region := 175, targets := 256 }], pairs := [(0,8),(1,8),(2,8),(3,8)], upper := (rows 97 7 44 152 336 34 320 129 385), lower := (rows 97 7 44 152 336 34 320 128 256), losses := [] }

theorem u2132 : Upper (D 9) (R 9) [96,5,40,144,320,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2132 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2133 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 145 288 66 400 272), lower := (rows 97 7 44 200 145 288 66 128 256), losses := [] }

theorem u2133 : Upper (D 9) (R 9) [96,5,40,192,129,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2133 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2134 : PairBound 9 := { available := 258, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 7 44 200 145 288 80 386 258), lower := (rows 97 7 44 200 145 288 80 128 256), losses := [] }

theorem u2134 : Upper (D 9) (R 9) [96,5,40,192,129,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2134 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2135 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 200 145 288 320 146 274), lower := (rows 97 7 44 200 145 288 320 128 256), losses := [] }

theorem u2135 : Upper (D 9) (R 9) [96,5,40,192,129,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2135 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2136 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 7 44 200 146 288 65 400 272), lower := (rows 97 7 44 200 146 288 65 128 256), losses := [] }

theorem u2136 : Upper (D 9) (R 9) [96,5,40,192,130,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2136 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2137 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 295, targets := 128 },{ cop := 4, region := 72, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0)], upper := (rows 97 7 44 200 146 288 80 385 257), lower := (rows 97 7 44 200 146 288 80 128 256), losses := [] }

theorem u2137 : Upper (D 9) (R 9) [96,5,40,192,130,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2137 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2138 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 158, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8),(4,8)], upper := (rows 97 7 44 200 146 288 320 145 273), lower := (rows 97 7 44 200 146 288 320 128 256), losses := [] }

theorem u2138 : Upper (D 9) (R 9) [96,5,40,192,130,256,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2138 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2139 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 273 288 66 144 400), lower := (rows 97 7 44 200 273 288 66 128 256), losses := [] }

theorem u2139 : Upper (D 9) (R 9) [96,5,40,192,257,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2139 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2140 : PairBound 9 := { available := 130, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 200 273 288 80 130 386), lower := (rows 97 7 44 200 273 288 80 128 256), losses := [] }

theorem u2140 : Upper (D 9) (R 9) [96,5,40,192,257,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2140 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2141 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 7 44 200 273 288 192 146 274), lower := (rows 97 7 44 200 273 288 192 128 256), losses := [] }

theorem u2141 : Upper (D 9) (R 9) [96,5,40,192,257,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2141 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2142 : PairBound 9 := { available := 384, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 274 48 65 384 384), lower := (rows 97 7 44 200 274 48 65 128 256), losses := [] }

theorem u2142 : Upper (D 9) (R 9) [96,5,40,192,258,16,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2142 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2143 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7),(1,7),(2,7),(4,7)], upper := (rows 97 7 44 200 274 48 192 385 257), lower := (rows 97 7 44 200 274 48 192 128 256), losses := [] }

theorem u2143 : Upper (D 9) (R 9) [96,5,40,192,258,16,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2143 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2144 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 456, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 200 274 48 320 129 385), lower := (rows 97 7 44 200 274 48 320 128 256), losses := [] }

theorem u2144 : Upper (D 9) (R 9) [96,5,40,192,258,16,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2144 [(5,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2145 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 7 44 200 274 288 65 144 400), lower := (rows 97 7 44 200 274 288 65 128 256), losses := [] }

theorem u2145 : Upper (D 9) (R 9) [96,5,40,192,258,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2145 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2146 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 1, region := 472, targets := 32 }], pairs := [(1,8),(2,8),(3,5),(3,8)], upper := (rows 97 7 44 200 274 288 80 129 385), lower := (rows 97 7 44 200 274 288 80 128 256), losses := [] }

theorem u2146 : Upper (D 9) (R 9) [96,5,40,192,258,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2146 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2147 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 311, targets := 128 },{ cop := 6, region := 8, targets := 1 }], pairs := [(0,7),(1,7),(2,7),(3,0),(4,7)], upper := (rows 97 7 44 200 274 288 192 145 273), lower := (rows 97 7 44 200 274 288 192 128 256), losses := [] }

theorem u2147 : Upper (D 9) (R 9) [96,5,40,192,258,256,128] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2147 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2148 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 67, targets := 384 },{ cop := 1, region := 400, targets := 1 }], pairs := [(0,7),(0,8),(1,7),(1,8),(4,0)], upper := (rows 97 7 44 200 400 288 65 146 274), lower := (rows 97 7 44 200 400 288 65 128 256), losses := [] }

theorem u2148 : Upper (D 9) (R 9) [96,5,40,192,384,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2148 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2149 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 200 400 288 66 145 273), lower := (rows 97 7 44 200 400 288 66 128 256), losses := [] }

theorem u2149 : Upper (D 9) (R 9) [96,5,40,192,384,256,2] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2149 [(6,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2150 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 142, targets := 256 },{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,8)], upper := (rows 97 7 44 200 400 288 80 131 259), lower := (rows 97 7 44 200 400 288 80 128 256), losses := [] }

theorem u2150 : Upper (D 9) (R 9) [96,5,40,192,384,256,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2150 [(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2151 : PairBound 9 := { available := 320, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 44 392 145 34 80 448 320), lower := (rows 97 7 44 392 145 34 80 128 256), losses := [] }

theorem u2151 : Upper (D 9) (R 9) [96,5,40,384,129,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2151 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2152 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 7 44 392 145 34 320 208 336), lower := (rows 97 7 44 392 145 34 320 128 256), losses := [] }

theorem u2152 : Upper (D 9) (R 9) [96,5,40,384,129,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2152 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2153 : PairBound 9 := { available := 272, camps := [{ cop := 2, region := 67, targets := 384 }], pairs := [(0,7),(0,8),(1,7),(1,8)], upper := (rows 97 7 44 392 208 34 65 400 272), lower := (rows 97 7 44 392 208 34 65 128 256), losses := [] }

theorem u2153 : Upper (D 9) (R 9) [96,5,40,384,192,2,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2153 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2154 : PairBound 9 := { available := 257, camps := [{ cop := 3, region := 119, targets := 256 }], pairs := [(0,8),(1,8),(2,8)], upper := (rows 97 7 44 392 208 34 80 385 257), lower := (rows 97 7 44 392 208 34 80 128 256), losses := [] }

theorem u2154 : Upper (D 9) (R 9) [96,5,40,384,192,2,16] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2154 [(5,1),(6,4)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2155 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 103, targets := 128 },{ cop := 0, region := 408, targets := 32 }], pairs := [(0,7),(1,7),(2,7),(3,5)], upper := (rows 97 7 44 392 208 34 320 145 273), lower := (rows 97 7 44 392 208 34 320 128 256), losses := [] }

theorem u2155 : Upper (D 9) (R 9) [96,5,40,384,192,2,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2155 [(5,1)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2156 : PairBound 9 := { available := 96, camps := [{ cop := 0, region := 134, targets := 256 },{ cop := 4, region := 105, targets := 128 }], pairs := [(0,7),(1,8),(2,8),(3,7)], upper := (rows 97 7 134 25 400 40 320 224 352), lower := (rows 97 7 134 25 400 40 320 128 256), losses := [] }

theorem u2156 : Upper (D 9) (R 9) [96,5,130,17,384,8,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2156 [(5,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2157 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 414, targets := 64 },{ cop := 4, region := 97, targets := 128 }], pairs := [(0,7),(1,6),(2,6),(3,6),(4,6)], upper := (rows 97 7 134 25 400 96 320 168 296), lower := (rows 97 7 134 25 400 96 320 128 256), losses := [] }

theorem u2157 : Upper (D 9) (R 9) [96,5,130,17,384,64,256] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2157 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2158 : PairBound 9 := { available := 264, camps := [{ cop := 0, region := 408, targets := 1 },{ cop := 4, region := 297, targets := 128 },{ cop := 3, region := 65, targets := 256 }], pairs := [(0,7),(0,8),(3,0),(3,7),(4,0)], upper := (rows 97 7 134 56 208 288 65 392 264), lower := (rows 97 7 134 56 208 288 65 128 256), losses := [] }

theorem u2158 : Upper (D 9) (R 9) [96,5,130,48,192,256,1] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2158 []
    (constants 9).1 (constants 9).2 (by decide +kernel)

def b2159 : PairBound 9 := { available := 257, camps := [{ cop := 0, region := 406, targets := 32 },{ cop := 0, region := 390, targets := 64 }], pairs := [(1,5),(1,6),(2,5),(4,5)], upper := (rows 97 7 134 56 208 288 72 385 257), lower := (rows 97 7 134 56 208 288 72 128 256), losses := [] }

theorem u2159 : Upper (D 9) (R 9) [96,5,130,48,192,256,8] 13 :=
  CornerWitnessNine.sound _ _ _ _ (leftConstant 9) 14 b2159 [(6,3)]
    (constants 9).1 (constants 9).2 (by decide +kernel)

#print axioms u2159
end Delivery.IrregularNine14.P09
