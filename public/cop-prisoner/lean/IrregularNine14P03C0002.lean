import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P03C0000

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b120 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 73 145 160 96 208 336), lower := (rows 35 7 268 73 145 160 96 128 256), losses := [] }

theorem u120 : Upper (D 3) (R 3) [34,5,264,65,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b120
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b121 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 268 73 208 160 65 176 304), lower := (rows 35 7 268 73 208 160 65 128 256), losses := [] }

theorem u121 : Upper (D 3) (R 3) [34,5,264,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b121
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b122 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 268 73 208 160 80 161 289), lower := (rows 35 7 268 73 208 160 80 128 256), losses := [] }

theorem u122 : Upper (D 3) (R 3) [34,5,264,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b122
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b123 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 406, targets := 32 }], pairs := [(1,5)], upper := (rows 35 7 268 73 208 160 96 145 273), lower := (rows 35 7 268 73 208 160 96 128 256), losses := [] }

theorem u123 : Upper (D 3) (R 3) [34,5,264,65,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b123
    (constants 3).1 (constants 3).2 (by decide +kernel)

def r124 : Route 9 := (fun mask => (mask,id))

def c124 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 16 => 4 | 64 => 6 | 256 => 8 | _ => 0)

theorem u124 : Upper (D 3) (R 3) [34,5,320,17,192,128,1] 13 := by
  apply FastRouting.sound _ _ [34,5,320,17,192,128,1] 13 (by decide) (choices 1) [8,32] r124 c124
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

def b125 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 324 25 208 160 72 161 289), lower := (rows 35 7 324 25 208 160 72 128 256), losses := [] }

theorem u125 : Upper (D 3) (R 3) [34,5,320,17,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b125
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b126 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 80, targets := 1 }], pairs := [(4,0)], upper := (rows 35 7 324 25 208 160 96 137 265), lower := (rows 35 7 324 25 208 160 96 128 256), losses := [] }

theorem u126 : Upper (D 3) (R 3) [34,5,320,17,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b126
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b127 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 35 7 324 88 145 160 65 168 296), lower := (rows 35 7 324 88 145 160 65 128 256), losses := [] }

theorem u127 : Upper (D 3) (R 3) [34,5,320,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b127
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b128 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 7 324 88 145 160 72 161 289), lower := (rows 35 7 324 88 145 160 72 128 256), losses := [] }

theorem u128 : Upper (D 3) (R 3) [34,5,320,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b128
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b129 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 104, targets := 1 }], pairs := [(3,0)], upper := (rows 35 7 324 88 145 160 96 137 265), lower := (rows 35 7 324 88 145 160 96 128 256), losses := [] }

theorem u129 : Upper (D 3) (R 3) [34,5,320,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b129
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b130 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 324 104 145 160 65 152 280), lower := (rows 35 7 324 104 145 160 65 128 256), losses := [] }

theorem u130 : Upper (D 3) (R 3) [34,5,320,96,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b130
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b131 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 7 324 104 145 160 72 145 273), lower := (rows 35 7 324 104 145 160 72 128 256), losses := [] }

theorem u131 : Upper (D 3) (R 3) [34,5,320,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b131
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b132 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 7 324 104 145 160 80 137 265), lower := (rows 35 7 324 104 145 160 80 128 256), losses := [] }

theorem u132 : Upper (D 3) (R 3) [34,5,320,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b132
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b133 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 7 324 104 152 160 65 145 273), lower := (rows 35 7 324 104 152 160 65 128 256), losses := [] }

theorem u133 : Upper (D 3) (R 3) [34,5,320,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b133
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b134 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 7 324 104 152 160 80 129 257), lower := (rows 35 7 324 104 152 160 80 128 256), losses := [] }

theorem u134 : Upper (D 3) (R 3) [34,5,320,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b134
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b135 : PairBound 9 := { available := 144, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 265 112 160 65 144 400), lower := (rows 35 14 69 265 112 160 65 128 256), losses := [] }

theorem u135 : Upper (D 3) (R 3) [34,12,65,257,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b135
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b136 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 14 69 265 112 160 80 129 385), lower := (rows 35 14 69 265 112 160 80 128 256), losses := [] }

theorem u136 : Upper (D 3) (R 3) [34,12,65,257,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b136
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b137 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 35 14 69 265 112 160 192 145 273), lower := (rows 35 14 69 265 112 160 192 128 256), losses := [] }

theorem u137 : Upper (D 3) (R 3) [34,12,65,257,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b137
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b138 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 14 69 265 145 160 80 224 352), lower := (rows 35 14 69 265 145 160 80 128 256), losses := [] }

theorem u138 : Upper (D 3) (R 3) [34,12,65,257,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b138
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b139 : PairBound 9 := { available := 80, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 265 145 160 96 208 336), lower := (rows 35 14 69 265 145 160 96 128 256), losses := [] }

theorem u139 : Upper (D 3) (R 3) [34,12,65,257,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b139
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b140 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 265 208 160 65 176 304), lower := (rows 35 14 69 265 208 160 65 128 256), losses := [] }

theorem u140 : Upper (D 3) (R 3) [34,12,65,257,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b140
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b141 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 14 69 265 208 160 80 161 289), lower := (rows 35 14 69 265 208 160 80 128 256), losses := [] }

theorem u141 : Upper (D 3) (R 3) [34,12,65,257,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b141
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b142 : PairBound 9 := { available := 17, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5)], upper := (rows 35 14 69 265 208 160 96 145 273), lower := (rows 35 14 69 265 208 160 96 128 256), losses := [] }

theorem u142 : Upper (D 3) (R 3) [34,12,65,257,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b142
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b143 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 67 13 152 273 160 68 224 352), lower := (rows 35 67 13 152 273 160 68 128 256), losses := [] }

theorem u143 : Upper (D 3) (R 3) [34,65,9,144,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b143
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b144 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 152 273 160 96 196 324), lower := (rows 35 67 13 152 273 160 96 128 256), losses := [] }

theorem u144 : Upper (D 3) (R 3) [34,65,9,144,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b144
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b145 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 152 336 160 65 164 292), lower := (rows 35 67 13 152 336 160 65 128 256), losses := [] }

theorem u145 : Upper (D 3) (R 3) [34,65,9,144,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b145
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b146 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 13 152 336 160 68 161 289), lower := (rows 35 67 13 152 336 160 68 128 256), losses := [] }

theorem u146 : Upper (D 3) (R 3) [34,65,9,144,320,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b146
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b147 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 152 336 160 96 133 261), lower := (rows 35 67 13 152 336 160 96 128 256), losses := [] }

theorem u147 : Upper (D 3) (R 3) [34,65,9,144,320,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b147
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b148 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 67 13 268 145 160 80 224 352), lower := (rows 35 67 13 268 145 160 80 128 256), losses := [] }

theorem u148 : Upper (D 3) (R 3) [34,65,9,260,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b148
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b149 : PairBound 9 := { available := 80, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 268 145 160 96 208 336), lower := (rows 35 67 13 268 145 160 96 128 256), losses := [] }

theorem u149 : Upper (D 3) (R 3) [34,65,9,260,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b149
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b150 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 268 208 160 65 176 304), lower := (rows 35 67 13 268 208 160 65 128 256), losses := [] }

theorem u150 : Upper (D 3) (R 3) [34,65,9,260,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b150
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b151 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 13 268 208 160 80 161 289), lower := (rows 35 67 13 268 208 160 80 128 256), losses := [] }

theorem u151 : Upper (D 3) (R 3) [34,65,9,260,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b151
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b152 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 268 208 160 96 145 273), lower := (rows 35 67 13 268 208 160 96 128 256), losses := [] }

theorem u152 : Upper (D 3) (R 3) [34,65,9,260,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b152
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b153 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 67 13 280 145 160 68 224 352), lower := (rows 35 67 13 280 145 160 68 128 256), losses := [] }

theorem u153 : Upper (D 3) (R 3) [34,65,9,272,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b153
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b154 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 280 145 160 96 196 324), lower := (rows 35 67 13 280 145 160 96 128 256), losses := [] }

theorem u154 : Upper (D 3) (R 3) [34,65,9,272,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b154
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b155 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 280 208 160 65 164 292), lower := (rows 35 67 13 280 208 160 65 128 256), losses := [] }

theorem u155 : Upper (D 3) (R 3) [34,65,9,272,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b155
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b156 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 13 280 208 160 68 161 289), lower := (rows 35 67 13 280 208 160 68 128 256), losses := [] }

theorem u156 : Upper (D 3) (R 3) [34,65,9,272,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b156
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b157 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 280 208 160 96 133 261), lower := (rows 35 67 13 280 208 160 96 128 256), losses := [] }

theorem u157 : Upper (D 3) (R 3) [34,65,9,272,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b157
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b158 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 13 392 84 160 65 176 304), lower := (rows 35 67 13 392 84 160 65 128 256), losses := [] }

theorem u158 : Upper (D 3) (R 3) [34,65,9,384,68,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b158
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b159 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 13 392 84 160 80 161 289), lower := (rows 35 67 13 392 84 160 80 128 256), losses := [] }

theorem u159 : Upper (D 3) (R 3) [34,65,9,384,68,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b159
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b160 : PairBound 9 := { available := 17, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 13 392 84 160 96 145 273), lower := (rows 35 67 13 392 84 160 96 128 256), losses := [] }

theorem u160 : Upper (D 3) (R 3) [34,65,9,384,68,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b160
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b161 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 35 67 28 137 273 160 68 224 352), lower := (rows 35 67 28 137 273 160 68 128 256), losses := [] }

theorem u161 : Upper (D 3) (R 3) [34,65,24,129,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b161
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b162 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 28 137 273 160 96 196 324), lower := (rows 35 67 28 137 273 160 96 128 256), losses := [] }

theorem u162 : Upper (D 3) (R 3) [34,65,24,129,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b162
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b163 : PairBound 9 := { available := 68, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 137 304 160 65 196 324), lower := (rows 35 67 28 137 304 160 65 128 256), losses := [] }

theorem u163 : Upper (D 3) (R 3) [34,65,24,129,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b163
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b164 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 67 28 137 304 160 68 193 321), lower := (rows 35 67 28 137 304 160 68 128 256), losses := [] }

theorem u164 : Upper (D 3) (R 3) [34,65,24,129,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b164
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b165 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 137 336 160 65 164 292), lower := (rows 35 67 28 137 336 160 65 128 256), losses := [] }

theorem u165 : Upper (D 3) (R 3) [34,65,24,129,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b165
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b166 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 28 137 336 160 68 161 289), lower := (rows 35 67 28 137 336 160 68 128 256), losses := [] }

theorem u166 : Upper (D 3) (R 3) [34,65,24,129,320,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b166
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b167 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 28 137 336 160 96 133 261), lower := (rows 35 67 28 137 336 160 96 128 256), losses := [] }

theorem u167 : Upper (D 3) (R 3) [34,65,24,129,320,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b167
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b168 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 200 273 160 65 164 292), lower := (rows 35 67 28 200 273 160 65 128 256), losses := [] }

theorem u168 : Upper (D 3) (R 3) [34,65,24,192,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b168
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b169 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 67 28 200 273 160 68 161 289), lower := (rows 35 67 28 200 273 160 68 128 256), losses := [] }

theorem u169 : Upper (D 3) (R 3) [34,65,24,192,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b169
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b170 : PairBound 9 := { available := 5, camps := [{ cop := 1, region := 412, targets := 32 }], pairs := [(2,5)], upper := (rows 35 67 28 200 273 160 96 133 261), lower := (rows 35 67 28 200 273 160 96 128 256), losses := [] }

theorem u170 : Upper (D 3) (R 3) [34,65,24,192,257,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b170
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b171 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 28 200 304 160 65 133 261), lower := (rows 35 67 28 200 304 160 65 128 256), losses := [] }

theorem u171 : Upper (D 3) (R 3) [34,65,24,192,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b171
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b172 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 67 28 200 304 160 68 129 257), lower := (rows 35 67 28 200 304 160 68 128 256), losses := [] }

theorem u172 : Upper (D 3) (R 3) [34,65,24,192,288,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b172
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b173 : PairBound 9 := { available := 132, camps := [{ cop := 4, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 35 67 44 88 273 160 65 132 388), lower := (rows 35 67 44 88 273 160 65 128 256), losses := [] }

theorem u173 : Upper (D 3) (R 3) [34,65,40,80,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b173
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b174 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 88 273 160 68 129 385), lower := (rows 35 67 44 88 273 160 68 128 256), losses := [] }

theorem u174 : Upper (D 3) (R 3) [34,65,40,80,257,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b174
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b175 : PairBound 9 := { available := 5, camps := [], pairs := [(2,0)], upper := (rows 35 67 44 88 273 160 192 133 261), lower := (rows 35 67 44 88 273 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 16 224 224 128 256), good := (rows 98 98 108 124 272 224 224 224 256) }] }

theorem u175 : Upper (D 3) (R 3) [34,65,40,80,257,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b175
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b176 : PairBound 9 := { available := 144, camps := [{ cop := 2, region := 67, targets := 128 }], pairs := [(0,7)], upper := (rows 35 67 44 265 84 160 65 144 400), lower := (rows 35 67 44 265 84 160 65 128 256), losses := [] }

theorem u176 : Upper (D 3) (R 3) [34,65,40,257,68,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b176
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b177 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 67 44 265 84 160 80 129 385), lower := (rows 35 67 44 265 84 160 80 128 256), losses := [] }

theorem u177 : Upper (D 3) (R 3) [34,65,40,257,68,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b177
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b178 : PairBound 9 := { available := 17, camps := [], pairs := [(4,0)], upper := (rows 35 67 44 265 84 160 192 145 273), lower := (rows 35 67 44 265 84 160 192 128 256), losses := [{ target := 0, region := (rows 0 2 4 8 20 224 224 128 256), good := (rows 98 98 124 264 116 224 224 224 256) }] }

theorem u178 : Upper (D 3) (R 3) [34,65,40,257,68,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b178
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b179 : PairBound 9 := { available := 80, camps := [], pairs := [], upper := (rows 35 67 44 265 145 160 68 208 336), lower := (rows 35 67 44 265 145 160 68 128 256), losses := [] }

theorem u179 : Upper (D 3) (R 3) [34,65,40,257,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b179
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u179
end Delivery.IrregularNine14.P03
