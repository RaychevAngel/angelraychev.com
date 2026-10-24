import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 290, targets := 16 }], pairs := [(1,4)], upper := (rows 53 266 7 200 80 160 80 162 290), lower := (rows 53 266 7 200 80 160 80 128 256), losses := [] }

theorem u120 : Upper (D 1) (R 1) [52,264,3,192,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b120
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 18, camps := [{ cop := 4, region := 394, targets := 32 }], pairs := [(1,5)], upper := (rows 53 266 7 200 80 160 96 146 274), lower := (rows 53 266 7 200 80 160 96 128 256), losses := [] }

theorem u121 : Upper (D 1) (R 1) [52,264,3,192,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b121
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 14 148 296 18 160 65 194 322), lower := (rows 113 14 148 296 18 160 65 128 256), losses := [] }

theorem u122 : Upper (D 1) (R 1) [112,12,144,288,2,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b122
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 132, targets := 2 }], pairs := [(2,1)], upper := (rows 113 14 148 296 18 160 66 193 321), lower := (rows 113 14 148 296 18 160 66 128 256), losses := [] }

theorem u123 : Upper (D 1) (R 1) [112,12,144,288,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b123
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 113 22 44 328 144 34 65 130 386), lower := (rows 113 22 44 328 144 34 65 128 256), losses := [] }

theorem u124 : Upper (D 1) (R 1) [112,20,40,320,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b124
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 44 328 144 34 66 129 385), lower := (rows 113 22 44 328 144 34 66 128 256), losses := [] }

theorem u125 : Upper (D 1) (R 1) [112,20,40,320,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b125
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 44 328 144 34 192 131 259), lower := (rows 113 22 44 328 144 34 192 128 256), losses := [] }

theorem u126 : Upper (D 1) (R 1) [112,20,40,320,128,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b126
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 113 22 292 74 144 34 65 136 392), lower := (rows 113 22 292 74 144 34 65 128 256), losses := [] }

theorem u127 : Upper (D 1) (R 1) [112,20,288,66,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b127
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 113 22 292 74 144 34 72 129 385), lower := (rows 113 22 292 74 144 34 72 128 256), losses := [] }

theorem u128 : Upper (D 1) (R 1) [112,20,288,66,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b128
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 270, targets := 128 }], pairs := [(1,7)], upper := (rows 113 22 292 74 144 34 192 137 265), lower := (rows 113 22 292 74 144 34 192 128 256), losses := [] }

theorem u129 : Upper (D 1) (R 1) [112,20,288,66,128,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b129
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 292 137 144 34 66 200 328), lower := (rows 113 22 292 137 144 34 66 128 256), losses := [] }

theorem u130 : Upper (D 1) (R 1) [112,20,288,129,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b130
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 22 292 137 144 34 72 194 322), lower := (rows 113 22 292 137 144 34 72 128 256), losses := [] }

theorem u131 : Upper (D 1) (R 1) [112,20,288,129,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b131
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 113 22 292 138 144 34 65 200 328), lower := (rows 113 22 292 138 144 34 65 128 256), losses := [] }

theorem u132 : Upper (D 1) (R 1) [112,20,288,130,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b132
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 22 292 138 144 34 72 193 321), lower := (rows 113 22 292 138 144 34 72 128 256), losses := [] }

theorem u133 : Upper (D 1) (R 1) [112,20,288,130,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b133
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 113 22 292 200 144 34 65 138 266), lower := (rows 113 22 292 200 144 34 65 128 256), losses := [] }

theorem u134 : Upper (D 1) (R 1) [112,20,288,192,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b134
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 396, targets := 2 }], pairs := [(2,1)], upper := (rows 113 22 292 200 144 34 66 137 265), lower := (rows 113 22 292 200 144 34 66 128 256), losses := [] }

theorem u135 : Upper (D 1) (R 1) [112,20,288,192,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b135
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 22 292 200 144 34 72 131 259), lower := (rows 113 22 292 200 144 34 72 128 256), losses := [] }

theorem u136 : Upper (D 1) (R 1) [112,20,288,192,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b136
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 134 28 296 18 160 65 194 322), lower := (rows 113 134 28 296 18 160 65 128 256), losses := [] }

theorem u137 : Upper (D 1) (R 1) [112,132,24,288,2,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b137
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 28 296 18 160 66 193 321), lower := (rows 113 134 28 296 18 160 66 128 256), losses := [] }

theorem u138 : Upper (D 1) (R 1) [112,132,24,288,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b138
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 113 134 28 296 144 34 65 194 322), lower := (rows 113 134 28 296 144 34 65 128 256), losses := [] }

theorem u139 : Upper (D 1) (R 1) [112,132,24,288,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b139
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 65, camps := [{ cop := 0, region := 268, targets := 2 }], pairs := [(2,1)], upper := (rows 113 134 28 296 144 34 66 193 321), lower := (rows 113 134 28 296 144 34 66 128 256), losses := [] }

theorem u140 : Upper (D 1) (R 1) [112,132,24,288,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b140
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 134 276 11 18 40 192 224 352), lower := (rows 113 134 276 11 18 40 192 128 256), losses := [] }

theorem u141 : Upper (D 1) (R 1) [112,132,272,3,2,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b141
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 134 276 11 18 96 192 168 296), lower := (rows 113 134 276 11 18 96 192 128 256), losses := [] }

theorem u142 : Upper (D 1) (R 1) [112,132,272,3,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b142
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 134 276 11 144 34 72 224 352), lower := (rows 113 134 276 11 144 34 72 128 256), losses := [] }

theorem u143 : Upper (D 1) (R 1) [112,132,272,3,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b143
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 134 276 11 144 34 96 200 328), lower := (rows 113 134 276 11 144 34 96 128 256), losses := [] }

theorem u144 : Upper (D 1) (R 1) [112,132,272,3,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b144
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 259 14 152 18 36 192 224 352), lower := (rows 113 259 14 152 18 36 192 128 256), losses := [] }

theorem u145 : Upper (D 1) (R 1) [112,257,10,144,2,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b145
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 259 14 152 18 96 192 164 292), lower := (rows 113 259 14 152 18 96 192 128 256), losses := [] }

theorem u146 : Upper (D 1) (R 1) [112,257,10,144,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b146
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 262 148 11 18 40 192 224 352), lower := (rows 113 262 148 11 18 40 192 128 256), losses := [] }

theorem u147 : Upper (D 1) (R 1) [112,260,144,3,2,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b147
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 398, targets := 64 }], pairs := [(1,6)], upper := (rows 113 262 148 11 18 96 192 168 296), lower := (rows 113 262 148 11 18 96 192 128 256), losses := [] }

theorem u148 : Upper (D 1) (R 1) [112,260,144,3,2,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b148
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 274 13 138 144 34 68 224 352), lower := (rows 113 274 13 138 144 34 68 128 256), losses := [] }

theorem u149 : Upper (D 1) (R 1) [112,272,9,130,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b149
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 13 138 144 34 96 196 324), lower := (rows 113 274 13 138 144 34 96 128 256), losses := [] }

theorem u150 : Upper (D 1) (R 1) [112,272,9,130,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b150
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 113 274 14 137 144 34 68 224 352), lower := (rows 113 274 14 137 144 34 68 128 256), losses := [] }

theorem u151 : Upper (D 1) (R 1) [112,272,10,129,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b151
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 398, targets := 32 }], pairs := [(1,5)], upper := (rows 113 274 14 137 144 34 96 196 324), lower := (rows 113 274 14 137 144 34 96 128 256), losses := [] }

theorem u152 : Upper (D 1) (R 1) [112,272,10,129,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b152
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 68, camps := [], pairs := [], upper := (rows 113 274 14 168 144 34 65 196 324), lower := (rows 113 274 14 168 144 34 65 128 256), losses := [] }

theorem u153 : Upper (D 1) (R 1) [112,272,10,160,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b153
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 113 274 14 168 144 34 68 193 321), lower := (rows 113 274 14 168 144 34 68 128 256), losses := [] }

theorem u154 : Upper (D 1) (R 1) [112,272,10,160,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b154
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 113 274 44 200 144 34 65 134 262), lower := (rows 113 274 44 200 144 34 65 128 256), losses := [] }

theorem u155 : Upper (D 1) (R 1) [112,272,40,192,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b155
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 113 274 44 200 144 34 66 133 261), lower := (rows 113 274 44 200 144 34 66 128 256), losses := [] }

theorem u156 : Upper (D 1) (R 1) [112,272,40,192,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b156
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 113 274 44 200 144 34 68 131 259), lower := (rows 113 274 44 200 144 34 68 128 256), losses := [] }

theorem u157 : Upper (D 1) (R 1) [112,272,40,192,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b157
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 144, camps := [], pairs := [], upper := (rows 263 26 100 168 80 34 65 144 400), lower := (rows 263 26 100 168 80 34 65 128 256), losses := [] }

theorem u158 : Upper (D 1) (R 1) [262,24,96,160,64,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b158
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 129, camps := [{ cop := 0, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 263 26 100 168 80 34 80 129 385), lower := (rows 263 26 100 168 80 34 80 128 256), losses := [] }

theorem u159 : Upper (D 1) (R 1) [262,24,96,160,64,2,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b159
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 2 }], pairs := [(2,1)], upper := (rows 263 26 100 168 80 34 192 145 273), lower := (rows 263 26 100 168 80 34 192 128 256), losses := [] }

theorem u160 : Upper (D 1) (R 1) [262,24,96,160,64,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b160
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 263 50 76 138 80 160 65 176 304), lower := (rows 263 50 76 138 80 160 65 128 256), losses := [] }

theorem u161 : Upper (D 1) (R 1) [262,48,72,130,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b161
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 263 50 76 138 80 160 80 161 289), lower := (rows 263 50 76 138 80 160 80 128 256), losses := [] }

theorem u162 : Upper (D 1) (R 1) [262,48,72,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b162
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 100, targets := 2 }], pairs := [(2,1)], upper := (rows 263 50 76 138 80 160 96 145 273), lower := (rows 263 50 76 138 80 160 96 128 256), losses := [] }

theorem u163 : Upper (D 1) (R 1) [262,48,72,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b163
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 269 50 70 138 80 160 65 176 304), lower := (rows 269 50 70 138 80 160 65 128 256), losses := [] }

theorem u164 : Upper (D 1) (R 1) [268,48,66,130,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b164
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 33, camps := [{ cop := 2, region := 425, targets := 16 }], pairs := [(0,4)], upper := (rows 269 50 70 138 80 160 80 161 289), lower := (rows 269 50 70 138 80 160 80 128 256), losses := [] }

theorem u165 : Upper (D 1) (R 1) [268,48,66,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b165
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 409, targets := 32 }], pairs := [(0,5)], upper := (rows 269 50 70 138 80 160 96 145 273), lower := (rows 269 50 70 138 80 160 96 128 256), losses := [] }

theorem u166 : Upper (D 1) (R 1) [268,48,66,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b166
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 136, camps := [{ cop := 1, region := 84, targets := 128 }], pairs := [(2,7)], upper := (rows 275 35 52 76 80 160 66 136 392), lower := (rows 275 35 52 76 80 160 66 128 256), losses := [] }

theorem u167 : Upper (D 1) (R 1) [274,33,48,68,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b167
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 275 35 52 76 80 160 72 130 386), lower := (rows 275 35 52 76 80 160 72 128 256), losses := [] }

theorem u168 : Upper (D 1) (R 1) [274,33,48,68,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b168
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 84, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 76 80 160 192 138 266), lower := (rows 275 35 52 76 80 160 192 128 256), losses := [] }

theorem u169 : Upper (D 1) (R 1) [274,33,48,68,64,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b169
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 35 52 76 144 96 66 136 392), lower := (rows 275 35 52 76 144 96 66 128 256), losses := [] }

theorem u170 : Upper (D 1) (R 1) [274,33,48,68,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b170
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 275 35 52 76 144 96 72 130 386), lower := (rows 275 35 52 76 144 96 72 128 256), losses := [] }

theorem u171 : Upper (D 1) (R 1) [274,33,48,68,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b171
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 100, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 52 76 144 96 192 138 266), lower := (rows 275 35 52 76 144 96 192 128 256), losses := [] }

theorem u172 : Upper (D 1) (R 1) [274,33,48,68,128,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b172
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 172, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 152 80 160 66 164 292), lower := (rows 275 35 76 152 80 160 66 128 256), losses := [] }

theorem u173 : Upper (D 1) (R 1) [274,33,72,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b173
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 275 35 76 152 80 160 68 162 290), lower := (rows 275 35 76 152 80 160 68 128 256), losses := [] }

theorem u174 : Upper (D 1) (R 1) [274,33,72,144,64,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b174
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 6, camps := [{ cop := 5, region := 92, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 152 80 160 96 134 262), lower := (rows 275 35 76 152 80 160 96 128 256), losses := [] }

theorem u175 : Upper (D 1) (R 1) [274,33,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b175
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 275 35 76 168 144 96 66 148 276), lower := (rows 275 35 76 168 144 96 66 128 256), losses := [] }

theorem u176 : Upper (D 1) (R 1) [274,33,72,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b176
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 18, camps := [], pairs := [], upper := (rows 275 35 76 168 144 96 68 146 274), lower := (rows 275 35 76 168 144 96 68 128 256), losses := [] }

theorem u177 : Upper (D 1) (R 1) [274,33,72,160,128,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b177
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 6, camps := [{ cop := 4, region := 108, targets := 2 }], pairs := [(2,1)], upper := (rows 275 35 76 168 144 96 80 134 262), lower := (rows 275 35 76 168 144 96 80 128 256), losses := [] }

theorem u178 : Upper (D 1) (R 1) [274,33,72,160,128,64,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b178
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 35 84 168 144 96 66 140 268), lower := (rows 275 35 84 168 144 96 66 128 256), losses := [] }

theorem u179 : Upper (D 1) (R 1) [274,33,80,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b179
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P01
