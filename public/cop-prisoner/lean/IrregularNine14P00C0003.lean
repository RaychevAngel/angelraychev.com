import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P00C0000

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b180 : PairBound 9 := { available := 130, camps := [{ cop := 2, region := 170, targets := 1 }], pairs := [(1,0)], upper := (rows 305 14 84 168 17 96 65 130 386), lower := (rows 305 14 84 168 17 96 65 128 256), losses := [] }

theorem u180 : Upper (D 0) (R 0) [304,12,80,160,1,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b180
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b181 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 305 14 84 168 17 96 66 129 385), lower := (rows 305 14 84 168 17 96 66 128 256), losses := [] }

theorem u181 : Upper (D 0) (R 0) [304,12,80,160,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b181
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b182 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 40, targets := 1 }], pairs := [(3,0)], upper := (rows 305 14 84 168 17 96 192 131 259), lower := (rows 305 14 84 168 17 96 192 128 256), losses := [] }

theorem u182 : Upper (D 0) (R 0) [304,12,80,160,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b182
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b183 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 305 14 84 168 144 96 65 131 259), lower := (rows 305 14 84 168 144 96 65 128 256), losses := [] }

theorem u183 : Upper (D 0) (R 0) [304,12,80,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b183
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b184 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 305 14 84 168 144 96 66 129 257), lower := (rows 305 14 84 168 144 96 66 128 256), losses := [] }

theorem u184 : Upper (D 0) (R 0) [304,12,80,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b184
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b185 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 22 69 137 144 96 66 168 296), lower := (rows 305 22 69 137 144 96 66 128 256), losses := [] }

theorem u185 : Upper (D 0) (R 0) [304,20,65,129,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b185
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b186 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 22 69 137 144 96 72 162 290), lower := (rows 305 22 69 137 144 96 72 128 256), losses := [] }

theorem u186 : Upper (D 0) (R 0) [304,20,65,129,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b186
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b187 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 137 144 96 96 138 266), lower := (rows 305 22 69 137 144 96 96 128 256), losses := [] }

theorem u187 : Upper (D 0) (R 0) [304,20,65,129,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b187
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b188 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 138 144 96 65 168 296), lower := (rows 305 22 69 138 144 96 65 128 256), losses := [] }

theorem u188 : Upper (D 0) (R 0) [304,20,65,130,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b188
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b189 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 305 22 69 138 144 96 72 161 289), lower := (rows 305 22 69 138 144 96 72 128 256), losses := [] }

theorem u189 : Upper (D 0) (R 0) [304,20,65,130,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b189
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b190 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 154, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 138 144 96 96 137 265), lower := (rows 305 22 69 138 144 96 96 128 256), losses := [] }

theorem u190 : Upper (D 0) (R 0) [304,20,65,130,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b190
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b191 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 69 168 144 96 65 138 266), lower := (rows 305 22 69 168 144 96 65 128 256), losses := [] }

theorem u191 : Upper (D 0) (R 0) [304,20,65,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b191
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b192 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 22 69 168 144 96 66 137 265), lower := (rows 305 22 69 168 144 96 66 128 256), losses := [] }

theorem u192 : Upper (D 0) (R 0) [304,20,65,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b192
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b193 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 69 168 144 96 72 131 259), lower := (rows 305 22 69 168 144 96 72 128 256), losses := [] }

theorem u193 : Upper (D 0) (R 0) [304,20,65,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b193
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b194 : PairBound 9 := { available := 130, camps := [{ cop := 8, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 76 168 17 96 65 130 386), lower := (rows 305 22 76 168 17 96 65 128 256), losses := [] }

theorem u194 : Upper (D 0) (R 0) [304,20,72,160,1,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b194
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b195 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 305 22 76 168 17 96 66 129 385), lower := (rows 305 22 76 168 17 96 66 128 256), losses := [] }

theorem u195 : Upper (D 0) (R 0) [304,20,72,160,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b195
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b196 : PairBound 9 := { available := 3, camps := [{ cop := 6, region := 44, targets := 1 }], pairs := [(2,0)], upper := (rows 305 22 76 168 17 96 192 131 259), lower := (rows 305 22 76 168 17 96 192 128 256), losses := [] }

theorem u196 : Upper (D 0) (R 0) [304,20,72,160,1,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b196
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b197 : PairBound 9 := { available := 136, camps := [], pairs := [], upper := (rows 305 22 100 73 17 160 66 136 392), lower := (rows 305 22 100 73 17 160 66 128 256), losses := [] }

theorem u197 : Upper (D 0) (R 0) [304,20,96,65,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b197
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b198 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 22 100 73 17 160 72 130 386), lower := (rows 305 22 100 73 17 160 72 128 256), losses := [] }

theorem u198 : Upper (D 0) (R 0) [304,20,96,65,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b198
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b199 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 283, targets := 128 }], pairs := [(0,7)], upper := (rows 305 22 100 73 17 160 192 138 266), lower := (rows 305 22 100 73 17 160 192 128 256), losses := [] }

theorem u199 : Upper (D 0) (R 0) [304,20,96,65,1,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b199
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b200 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 305 22 100 137 17 160 66 200 328), lower := (rows 305 22 100 137 17 160 66 128 256), losses := [] }

theorem u200 : Upper (D 0) (R 0) [304,20,96,129,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b200
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b201 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 305 22 100 137 17 160 72 194 322), lower := (rows 305 22 100 137 17 160 72 128 256), losses := [] }

theorem u201 : Upper (D 0) (R 0) [304,20,96,129,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b201
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b202 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 305 22 100 137 144 33 66 200 328), lower := (rows 305 22 100 137 144 33 66 128 256), losses := [] }

theorem u202 : Upper (D 0) (R 0) [304,20,96,129,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b202
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b203 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 305 22 100 137 144 33 72 194 322), lower := (rows 305 22 100 137 144 33 72 128 256), losses := [] }

theorem u203 : Upper (D 0) (R 0) [304,20,96,129,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b203
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b204 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 138 17 160 65 200 328), lower := (rows 305 22 100 138 17 160 65 128 256), losses := [] }

theorem u204 : Upper (D 0) (R 0) [304,20,96,130,1,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b204
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b205 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 305 22 100 138 17 160 72 193 321), lower := (rows 305 22 100 138 17 160 72 128 256), losses := [] }

theorem u205 : Upper (D 0) (R 0) [304,20,96,130,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b205
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b206 : PairBound 9 := { available := 72, camps := [{ cop := 2, region := 154, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 138 144 33 65 200 328), lower := (rows 305 22 100 138 144 33 65 128 256), losses := [] }

theorem u206 : Upper (D 0) (R 0) [304,20,96,130,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b206
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b207 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 305 22 100 138 144 33 72 193 321), lower := (rows 305 22 100 138 144 33 72 128 256), losses := [] }

theorem u207 : Upper (D 0) (R 0) [304,20,96,130,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b207
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b208 : PairBound 9 := { available := 10, camps := [{ cop := 2, region := 154, targets := 1 }], pairs := [(1,0)], upper := (rows 305 22 100 200 144 33 65 138 266), lower := (rows 305 22 100 200 144 33 65 128 256), losses := [] }

theorem u208 : Upper (D 0) (R 0) [304,20,96,192,128,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b208
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b209 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 22 100 200 144 33 66 137 265), lower := (rows 305 22 100 200 144 33 66 128 256), losses := [] }

theorem u209 : Upper (D 0) (R 0) [304,20,96,192,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b209
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b210 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 100 200 144 33 72 131 259), lower := (rows 305 22 100 200 144 33 72 128 256), losses := [] }

theorem u210 : Upper (D 0) (R 0) [304,20,96,192,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b210
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b211 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 22 196 73 17 160 66 168 296), lower := (rows 305 22 196 73 17 160 66 128 256), losses := [] }

theorem u211 : Upper (D 0) (R 0) [304,20,192,65,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b211
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b212 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 22 196 73 17 160 72 162 290), lower := (rows 305 22 196 73 17 160 72 128 256), losses := [] }

theorem u212 : Upper (D 0) (R 0) [304,20,192,65,1,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b212
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b213 : PairBound 9 := { available := 10, camps := [{ cop := 3, region := 150, targets := 32 }], pairs := [(1,5)], upper := (rows 305 22 196 73 17 160 96 138 266), lower := (rows 305 22 196 73 17 160 96 128 256), losses := [] }

theorem u213 : Upper (D 0) (R 0) [304,20,192,65,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b213
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b214 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 305 67 76 152 17 160 66 164 292), lower := (rows 305 67 76 152 17 160 66 128 256), losses := [] }

theorem u214 : Upper (D 0) (R 0) [304,65,72,144,1,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b214
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b215 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 76 152 17 160 68 162 290), lower := (rows 305 67 76 152 17 160 68 128 256), losses := [] }

theorem u215 : Upper (D 0) (R 0) [304,65,72,144,1,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b215
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b216 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 76 152 17 160 96 134 262), lower := (rows 305 67 76 152 17 160 96 128 256), losses := [] }

theorem u216 : Upper (D 0) (R 0) [304,65,72,144,1,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b216
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b217 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 67 84 138 144 33 68 168 296), lower := (rows 305 67 84 138 144 33 68 128 256), losses := [] }

theorem u217 : Upper (D 0) (R 0) [304,65,80,130,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b217
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b218 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 305 67 84 138 144 33 72 164 292), lower := (rows 305 67 84 138 144 33 72 128 256), losses := [] }

theorem u218 : Upper (D 0) (R 0) [304,65,80,130,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b218
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b219 : PairBound 9 := { available := 12, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 84 138 144 33 96 140 268), lower := (rows 305 67 84 138 144 33 96 128 256), losses := [] }

theorem u219 : Upper (D 0) (R 0) [304,65,80,130,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b219
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b220 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 67 84 140 144 33 66 168 296), lower := (rows 305 67 84 140 144 33 66 128 256), losses := [] }

theorem u220 : Upper (D 0) (R 0) [304,65,80,132,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b220
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b221 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 84 140 144 33 72 162 290), lower := (rows 305 67 84 140 144 33 72 128 256), losses := [] }

theorem u221 : Upper (D 0) (R 0) [304,65,80,132,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b221
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b222 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 156, targets := 1 }], pairs := [(2,0)], upper := (rows 305 67 84 140 144 33 96 138 266), lower := (rows 305 67 84 140 144 33 96 128 256), losses := [] }

theorem u222 : Upper (D 0) (R 0) [304,65,80,132,128,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b222
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b223 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 305 67 84 168 144 33 66 140 268), lower := (rows 305 67 84 168 144 33 66 128 256), losses := [] }

theorem u223 : Upper (D 0) (R 0) [304,65,80,160,128,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b223
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b224 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 84 168 144 33 68 138 266), lower := (rows 305 67 84 168 144 33 68 128 256), losses := [] }

theorem u224 : Upper (D 0) (R 0) [304,65,80,160,128,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b224
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b225 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 84 168 144 33 72 134 262), lower := (rows 305 67 84 168 144 33 72 128 256), losses := [] }

theorem u225 : Upper (D 0) (R 0) [304,65,80,160,128,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b225
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b226 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 305 67 148 168 17 96 66 140 268), lower := (rows 305 67 148 168 17 96 66 128 256), losses := [] }

theorem u226 : Upper (D 0) (R 0) [304,65,144,160,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b226
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b227 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 148 168 17 96 68 138 266), lower := (rows 305 67 148 168 17 96 68 128 256), losses := [] }

theorem u227 : Upper (D 0) (R 0) [304,65,144,160,1,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b227
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b228 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 148 168 17 96 72 134 262), lower := (rows 305 67 148 168 17 96 72 128 256), losses := [] }

theorem u228 : Upper (D 0) (R 0) [304,65,144,160,1,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b228
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b229 : PairBound 9 := { available := 10, camps := [{ cop := 1, region := 168, targets := 1 }], pairs := [(3,0)], upper := (rows 305 70 148 168 17 96 65 138 266), lower := (rows 305 70 148 168 17 96 65 128 256), losses := [] }

theorem u229 : Upper (D 0) (R 0) [304,68,144,160,1,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b229
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b230 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 70 148 168 17 96 66 137 265), lower := (rows 305 70 148 168 17 96 66 128 256), losses := [] }

theorem u230 : Upper (D 0) (R 0) [304,68,144,160,1,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b230
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b231 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 17 96 72 131 259), lower := (rows 305 70 148 168 17 96 72 128 256), losses := [] }

theorem u231 : Upper (D 0) (R 0) [304,68,144,160,1,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b231
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b232 : PairBound 9 := { available := 10, camps := [{ cop := 8, region := 113, targets := 128 }], pairs := [(0,7)], upper := (rows 305 70 148 168 80 33 65 138 266), lower := (rows 305 70 148 168 80 33 65 128 256), losses := [] }

theorem u232 : Upper (D 0) (R 0) [304,68,144,160,64,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b232
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b233 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 305 70 148 168 80 33 66 137 265), lower := (rows 305 70 148 168 80 33 66 128 256), losses := [] }

theorem u233 : Upper (D 0) (R 0) [304,68,144,160,64,1,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b233
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b234 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 148 168 80 33 72 131 259), lower := (rows 305 70 148 168 80 33 72 128 256), losses := [] }

theorem u234 : Upper (D 0) (R 0) [304,68,144,160,64,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b234
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b235 : PairBound 9 := { available := 176, camps := [{ cop := 4, region := 226, targets := 1 }], pairs := [(1,0)], upper := (rows 15 50 196 265 17 96 240 176 432), lower := (rows 15 50 196 265 17 96 64 128 256), losses := [] }

theorem u235 : Upper (D 0) (R 0) [14,48,192,257,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b235
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b236 : PairBound 9 := { available := 145, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5)], upper := (rows 15 50 196 265 48 96 209 145 401), lower := (rows 15 50 196 265 48 96 64 128 256), losses := [] }

theorem u236 : Upper (D 0) (R 0) [14,48,192,257,32,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b236
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b237 : PairBound 9 := { available := 49, camps := [{ cop := 2, region := 50, targets := 1 }], pairs := [(1,0)], upper := (rows 15 50 196 265 80 160 113 177 305), lower := (rows 15 50 196 265 80 160 64 128 256), losses := [] }

theorem u237 : Upper (D 0) (R 0) [14,48,192,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b237
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b238 : PairBound 9 := { available := 208, camps := [{ cop := 5, region := 212, targets := 1 }], pairs := [(2,0)], upper := (rows 23 11 100 296 144 33 208 208 464), lower := (rows 23 11 100 296 144 33 64 128 256), losses := [] }

theorem u238 : Upper (D 0) (R 0) [22,9,96,288,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b238
    (constants 0).1 (constants 0).2 (by decide +kernel)

def r239 : Route 9 := (fun mask => (mask,id))

def c239 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 4 => 2 | 8 => 3 | 16 => 4 | 32 => 5 | 256 => 8 | _ => 0)

theorem u239 : Upper (D 0) (R 0) [22,9,96,288,128,16] 13 := by
  apply FastRouting.sound _ _ [22,9,96,288,128,16] 13 (by decide) (choices 1) [1,128] r239 c239
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact u0
  · exact u1

#print axioms u239
end Delivery.IrregularNine14.P00
