import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 275 35 84 168 144 96 72 133 261), lower := (rows 275 35 84 168 144 96 72 128 256), losses := [] }

theorem u120 : Upper (D 0) (R 0) [274,33,80,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b120
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 88 144 160 65 168 296), lower := (rows 275 38 69 88 144 160 65 128 256), losses := [] }

theorem u121 : Upper (D 0) (R 0) [274,36,65,80,128,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b121
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 275 38 69 88 144 160 72 161 289), lower := (rows 275 38 69 88 144 160 72 128 256), losses := [] }

theorem u122 : Upper (D 0) (R 0) [274,36,65,80,128,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b122
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 275 38 69 88 144 160 96 137 265), lower := (rows 275 38 69 88 144 160 96 128 256), losses := [] }

theorem u123 : Upper (D 0) (R 0) [274,36,65,80,128,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b123
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b124 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 16 }], pairs := [(2,4)], upper := (rows 275 38 69 104 144 160 65 152 280), lower := (rows 275 38 69 104 144 160 65 128 256), losses := [] }

theorem u124 : Upper (D 0) (R 0) [274,36,65,96,128,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b124
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b125 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 275 38 69 104 144 160 72 145 273), lower := (rows 275 38 69 104 144 160 72 128 256), losses := [] }

theorem u125 : Upper (D 0) (R 0) [274,36,65,96,128,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b125
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 275 38 69 104 144 160 80 137 265), lower := (rows 275 38 69 104 144 160 80 128 256), losses := [] }

theorem u126 : Upper (D 0) (R 0) [274,36,65,96,128,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b126
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 136, camps := [{ cop := 3, region := 134, targets := 1 }], pairs := [(1,0)], upper := (rows 275 38 196 104 17 48 65 136 392), lower := (rows 275 38 196 104 17 48 65 128 256), losses := [] }

theorem u127 : Upper (D 0) (R 0) [274,36,192,96,1,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b127
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 38 196 104 17 48 72 129 385), lower := (rows 275 38 196 104 17 48 72 128 256), losses := [] }

theorem u128 : Upper (D 0) (R 0) [274,36,192,96,1,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b128
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 315, targets := 128 }], pairs := [(0,7)], upper := (rows 275 38 196 104 17 48 192 137 265), lower := (rows 275 38 196 104 17 48 192 128 256), losses := [] }

theorem u129 : Upper (D 0) (R 0) [274,36,192,96,1,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b129
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 80, camps := [], pairs := [], upper := (rows 275 98 13 168 144 33 68 208 336), lower := (rows 275 98 13 168 144 33 68 128 256), losses := [] }

theorem u130 : Upper (D 0) (R 0) [274,96,9,160,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b130
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 98 13 168 144 33 80 196 324), lower := (rows 275 98 13 168 144 33 80 128 256), losses := [] }

theorem u131 : Upper (D 0) (R 0) [274,96,9,160,128,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b131
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 132, camps := [{ cop := 3, region := 166, targets := 1 }], pairs := [(1,0)], upper := (rows 275 98 44 88 17 160 65 132 388), lower := (rows 275 98 44 88 17 160 65 128 256), losses := [] }

theorem u132 : Upper (D 0) (R 0) [274,96,40,80,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b132
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 88 17 160 68 129 385), lower := (rows 275 98 44 88 17 160 68 128 256), losses := [] }

theorem u133 : Upper (D 0) (R 0) [274,96,40,80,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b133
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 285, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 88 17 160 192 133 261), lower := (rows 275 98 44 88 17 160 192 128 256), losses := [] }

theorem u134 : Upper (D 0) (R 0) [274,96,40,80,1,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b134
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 98, targets := 128 }], pairs := [(1,7)], upper := (rows 275 98 44 88 144 33 65 132 388), lower := (rows 275 98 44 88 144 33 65 128 256), losses := [] }

theorem u135 : Upper (D 0) (R 0) [274,96,40,80,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b135
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 88 144 33 68 129 385), lower := (rows 275 98 44 88 144 33 68 128 256), losses := [] }

theorem u136 : Upper (D 0) (R 0) [274,96,40,80,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b136
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 295, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 88 144 33 192 133 261), lower := (rows 275 98 44 88 144 33 192 128 256), losses := [] }

theorem u137 : Upper (D 0) (R 0) [274,96,40,80,128,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b137
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 132, camps := [{ cop := 1, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 44 200 17 48 65 132 388), lower := (rows 275 98 44 200 17 48 65 128 256), losses := [] }

theorem u138 : Upper (D 0) (R 0) [274,96,40,192,1,16,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b138
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 275 98 44 200 17 48 68 129 385), lower := (rows 275 98 44 200 17 48 68 128 256), losses := [] }

theorem u139 : Upper (D 0) (R 0) [274,96,40,192,1,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b139
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 5, camps := [{ cop := 3, region := 311, targets := 128 }], pairs := [(0,7)], upper := (rows 275 98 44 200 17 48 192 133 261), lower := (rows 275 98 44 200 17 48 192 128 256), losses := [] }

theorem u140 : Upper (D 0) (R 0) [274,96,40,192,1,16,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b140
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 98, targets := 16 }], pairs := [(1,4)], upper := (rows 275 98 44 200 144 33 65 148 276), lower := (rows 275 98 44 200 144 33 65 128 256), losses := [] }

theorem u141 : Upper (D 0) (R 0) [274,96,40,192,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b141
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 275 98 44 200 144 33 68 145 273), lower := (rows 275 98 44 200 144 33 68 128 256), losses := [] }

theorem u142 : Upper (D 0) (R 0) [274,96,40,192,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b142
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 5, camps := [{ cop := 4, region := 72, targets := 1 }], pairs := [(3,0)], upper := (rows 275 98 44 200 144 33 80 133 261), lower := (rows 275 98 44 200 144 33 80 128 256), losses := [] }

theorem u143 : Upper (D 0) (R 0) [274,96,40,192,128,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b143
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 72, camps := [], pairs := [(1,0)], upper := (rows 275 98 52 140 17 160 65 200 328), lower := (rows 275 98 52 140 17 160 65 128 256), losses := [{ target := 0, region := (rows 0 66 21 73 16 235 64 194 322), good := (rows 446 490 52 172 60 160 494 160 256) }] }

theorem u144 : Upper (D 0) (R 0) [274,96,48,132,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b144
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 275 98 52 140 17 160 72 193 321), lower := (rows 275 98 52 140 17 160 72 128 256), losses := [] }

theorem u145 : Upper (D 0) (R 0) [274,96,48,132,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b145
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 140, targets := 1 }], pairs := [(2,0)], upper := (rows 275 98 164 200 17 33 80 140 268), lower := (rows 275 98 164 200 17 33 80 128 256), losses := [] }

theorem u146 : Upper (D 0) (R 0) [274,96,160,192,1,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b146
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 275 98 164 200 17 36 80 137 265), lower := (rows 275 98 164 200 17 36 80 128 256), losses := [] }

theorem u147 : Upper (D 0) (R 0) [274,96,160,192,1,4,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b147
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 275 98 164 200 17 40 80 133 261), lower := (rows 275 98 164 200 17 40 80 128 256), losses := [] }

theorem u148 : Upper (D 0) (R 0) [274,96,160,192,1,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b148
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 305 7 76 137 80 160 66 176 304), lower := (rows 305 7 76 137 80 160 66 128 256), losses := [] }

theorem u149 : Upper (D 0) (R 0) [304,5,72,129,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b149
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 7 76 137 80 160 80 162 290), lower := (rows 305 7 76 137 80 160 80 128 256), losses := [] }

theorem u150 : Upper (D 0) (R 0) [304,5,72,129,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b150
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 102, targets := 16 }], pairs := [(1,4)], upper := (rows 305 7 76 137 80 160 96 146 274), lower := (rows 305 7 76 137 80 160 96 128 256), losses := [] }

theorem u151 : Upper (D 0) (R 0) [304,5,72,129,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b151
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 7 76 152 17 96 66 160 416), lower := (rows 305 7 76 152 17 96 66 128 256), losses := [] }

theorem u152 : Upper (D 0) (R 0) [304,5,72,144,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b152
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 130, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 152 17 96 96 130 386), lower := (rows 305 7 76 152 17 96 96 128 256), losses := [] }

theorem u153 : Upper (D 0) (R 0) [304,5,72,144,1,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b153
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 307, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 76 152 17 96 192 162 290), lower := (rows 305 7 76 152 17 96 192 128 256), losses := [] }

theorem u154 : Upper (D 0) (R 0) [304,5,72,144,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b154
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 7 76 152 17 160 66 224 352), lower := (rows 305 7 76 152 17 160 66 128 256), losses := [] }

theorem u155 : Upper (D 0) (R 0) [304,5,72,144,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b155
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 66, camps := [{ cop := 3, region := 100, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 152 17 160 96 194 322), lower := (rows 305 7 76 152 17 160 96 128 256), losses := [] }

theorem u156 : Upper (D 0) (R 0) [304,5,72,144,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b156
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 7 76 152 80 33 66 160 416), lower := (rows 305 7 76 152 80 33 66 128 256), losses := [] }

theorem u157 : Upper (D 0) (R 0) [304,5,72,144,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b157
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 305 7 76 152 80 33 96 130 386), lower := (rows 305 7 76 152 80 33 96 128 256), losses := [] }

theorem u158 : Upper (D 0) (R 0) [304,5,72,144,64,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b158
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 28, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 152 80 33 192 162 290), lower := (rows 305 7 76 152 80 33 192 128 256), losses := [] }

theorem u159 : Upper (D 0) (R 0) [304,5,72,144,64,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b159
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 34, camps := [], pairs := [(3,0)], upper := (rows 305 7 76 152 80 160 65 162 290), lower := (rows 305 7 76 152 80 160 65 128 256), losses := [{ target := 0, region := (rows 0 2 4 10 84 170 64 130 258), good := (rows 304 446 124 184 80 160 80 160 256) }] }

theorem u160 : Upper (D 0) (R 0) [304,5,72,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b160
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 305 7 76 152 80 160 66 161 289), lower := (rows 305 7 76 152 80 160 66 128 256), losses := [] }

theorem u161 : Upper (D 0) (R 0) [304,5,72,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b161
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 3, camps := [{ cop := 5, region := 92, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 76 152 80 160 96 131 259), lower := (rows 305 7 76 152 80 160 96 128 256), losses := [] }

theorem u162 : Upper (D 0) (R 0) [304,5,72,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b162
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 7 196 88 17 160 66 168 296), lower := (rows 305 7 196 88 17 160 66 128 256), losses := [] }

theorem u163 : Upper (D 0) (R 0) [304,5,192,80,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b163
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 7 196 88 17 160 72 162 290), lower := (rows 305 7 196 88 17 160 72 128 256), losses := [] }

theorem u164 : Upper (D 0) (R 0) [304,5,192,80,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b164
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 10, camps := [{ cop := 5, region := 68, targets := 1 }], pairs := [(2,0)], upper := (rows 305 7 196 88 17 160 96 138 266), lower := (rows 305 7 196 88 17 160 96 128 256), losses := [] }

theorem u165 : Upper (D 0) (R 0) [304,5,192,80,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b165
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 48, camps := [], pairs := [], upper := (rows 305 14 69 137 80 160 66 176 304), lower := (rows 305 14 69 137 80 160 66 128 256), losses := [] }

theorem u166 : Upper (D 0) (R 0) [304,12,65,129,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b166
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 34, camps := [{ cop := 2, region := 170, targets := 16 }], pairs := [(1,4)], upper := (rows 305 14 69 137 80 160 80 162 290), lower := (rows 305 14 69 137 80 160 80 128 256), losses := [] }

theorem u167 : Upper (D 0) (R 0) [304,12,65,129,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b167
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 18, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 137 80 160 96 146 274), lower := (rows 305 14 69 137 80 160 96 128 256), losses := [] }

theorem u168 : Upper (D 0) (R 0) [304,12,65,129,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b168
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 14 69 152 17 96 66 160 416), lower := (rows 305 14 69 152 17 96 66 128 256), losses := [] }

theorem u169 : Upper (D 0) (R 0) [304,12,65,144,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b169
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 152 17 96 96 130 386), lower := (rows 305 14 69 152 17 96 96 128 256), losses := [] }

theorem u170 : Upper (D 0) (R 0) [304,12,65,144,1,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b170
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 34, camps := [], pairs := [(0,7)], upper := (rows 305 14 69 152 17 96 192 162 290), lower := (rows 305 14 69 152 17 96 192 128 256), losses := [{ target := 7, region := (rows 3 2 4 8 23 100 64 0 258), good := (rows 305 319 117 24 17 96 96 0 256) }] }

theorem u171 : Upper (D 0) (R 0) [304,12,65,144,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b171
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 14 69 152 17 160 66 224 352), lower := (rows 305 14 69 152 17 160 66 128 256), losses := [] }

theorem u172 : Upper (D 0) (R 0) [304,12,65,144,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b172
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 152 17 160 96 194 322), lower := (rows 305 14 69 152 17 160 96 128 256), losses := [] }

theorem u173 : Upper (D 0) (R 0) [304,12,65,144,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b173
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 160, camps := [], pairs := [], upper := (rows 305 14 69 152 80 33 66 160 416), lower := (rows 305 14 69 152 80 33 66 128 256), losses := [] }

theorem u174 : Upper (D 0) (R 0) [304,12,65,144,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b174
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 154, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 69 152 80 33 96 130 386), lower := (rows 305 14 69 152 80 33 96 128 256), losses := [] }

theorem u175 : Upper (D 0) (R 0) [304,12,65,144,64,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b175
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 34, camps := [{ cop := 6, region := 24, targets := 1 }], pairs := [(3,0)], upper := (rows 305 14 69 152 80 33 192 162 290), lower := (rows 305 14 69 152 80 33 192 128 256), losses := [] }

theorem u176 : Upper (D 0) (R 0) [304,12,65,144,64,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b176
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 69 152 80 160 65 162 290), lower := (rows 305 14 69 152 80 160 65 128 256), losses := [] }

theorem u177 : Upper (D 0) (R 0) [304,12,65,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b177
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 305 14 69 152 80 160 66 161 289), lower := (rows 305 14 69 152 80 160 66 128 256), losses := [] }

theorem u178 : Upper (D 0) (R 0) [304,12,65,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b178
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 14 69 152 80 160 96 131 259), lower := (rows 305 14 69 152 80 160 96 128 256), losses := [] }

theorem u179 : Upper (D 0) (R 0) [304,12,65,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b179
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P00
