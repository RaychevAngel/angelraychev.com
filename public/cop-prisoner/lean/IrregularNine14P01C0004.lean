import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P01
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 409, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 137 144 96 66 168 296), lower := (rows 305 22 70 137 144 96 66 128 256), losses := [] }

theorem u240 : Upper (D 1) (R 1) [304,20,66,129,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b240
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 22 70 137 144 96 72 162 290), lower := (rows 305 22 70 137 144 96 72 128 256), losses := [] }

theorem u241 : Upper (D 1) (R 1) [304,20,66,129,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b241
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 70 137 144 96 96 138 266), lower := (rows 305 22 70 137 144 96 96 128 256), losses := [] }

theorem u242 : Upper (D 1) (R 1) [304,20,66,129,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b242
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 22 70 168 144 96 65 138 266), lower := (rows 305 22 70 168 144 96 65 128 256), losses := [] }

theorem u243 : Upper (D 1) (R 1) [304,20,66,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b243
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 409, targets := 2 }], pairs := [(0,1)], upper := (rows 305 22 70 168 144 96 66 137 265), lower := (rows 305 22 70 168 144 96 66 128 256), losses := [] }

theorem u244 : Upper (D 1) (R 1) [304,20,66,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b244
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 70 168 144 96 72 131 259), lower := (rows 305 22 70 168 144 96 72 128 256), losses := [] }

theorem u245 : Upper (D 1) (R 1) [304,20,66,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b245
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 136, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 73 144 34 66 136 392), lower := (rows 305 22 100 73 144 34 66 128 256), losses := [] }

theorem u246 : Upper (D 1) (R 1) [304,20,96,65,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b246
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 22 100 73 144 34 72 130 386), lower := (rows 305 22 100 73 144 34 72 128 256), losses := [] }

theorem u247 : Upper (D 1) (R 1) [304,20,96,65,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b247
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 10, camps := [], pairs := [(2,1)], upper := (rows 305 22 100 73 144 34 192 138 266), lower := (rows 305 22 100 73 144 34 192 128 256), losses := [{ target := 1, region := (rows 1 0 5 9 208 32 208 128 256), good := (rows 381 84 116 93 208 32 208 208 256) }] }

theorem u248 : Upper (D 1) (R 1) [304,20,96,65,128,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b248
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 72, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 137 144 34 66 200 328), lower := (rows 305 22 100 137 144 34 66 128 256), losses := [] }

theorem u249 : Upper (D 1) (R 1) [304,20,96,129,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b249
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 66, camps := [], pairs := [], upper := (rows 305 22 100 137 144 34 72 194 322), lower := (rows 305 22 100 137 144 34 72 128 256), losses := [] }

theorem u250 : Upper (D 1) (R 1) [304,20,96,129,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b250
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 72, camps := [], pairs := [], upper := (rows 305 22 100 138 144 34 65 200 328), lower := (rows 305 22 100 138 144 34 65 128 256), losses := [] }

theorem u251 : Upper (D 1) (R 1) [304,20,96,130,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b251
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 305 22 100 138 144 34 72 193 321), lower := (rows 305 22 100 138 144 34 72 128 256), losses := [] }

theorem u252 : Upper (D 1) (R 1) [304,20,96,130,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b252
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 22 100 200 144 34 65 138 266), lower := (rows 305 22 100 200 144 34 65 128 256), losses := [] }

theorem u253 : Upper (D 1) (R 1) [304,20,96,192,128,2,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b253
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 22 100 200 144 34 66 137 265), lower := (rows 305 22 100 200 144 34 66 128 256), losses := [] }

theorem u254 : Upper (D 1) (R 1) [304,20,96,192,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b254
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 22 100 200 144 34 72 131 259), lower := (rows 305 22 100 200 144 34 72 128 256), losses := [] }

theorem u255 : Upper (D 1) (R 1) [304,20,96,192,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b255
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 305 67 14 152 18 160 68 224 352), lower := (rows 305 67 14 152 18 160 68 128 256), losses := [] }

theorem u256 : Upper (D 1) (R 1) [304,65,10,144,2,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b256
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 68, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 14 152 18 160 96 196 324), lower := (rows 305 67 14 152 18 160 96 128 256), losses := [] }

theorem u257 : Upper (D 1) (R 1) [304,65,10,144,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b257
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 14 152 80 160 66 164 292), lower := (rows 305 67 14 152 80 160 66 128 256), losses := [] }

theorem u258 : Upper (D 1) (R 1) [304,65,10,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b258
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 14 152 80 160 68 162 290), lower := (rows 305 67 14 152 80 160 68 128 256), losses := [] }

theorem u259 : Upper (D 1) (R 1) [304,65,10,144,64,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b259
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 14 152 80 160 96 134 262), lower := (rows 305 67 14 152 80 160 96 128 256), losses := [] }

theorem u260 : Upper (D 1) (R 1) [304,65,10,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b260
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 132, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 67 28 104 18 160 66 132 388), lower := (rows 305 67 28 104 18 160 66 128 256), losses := [] }

theorem u261 : Upper (D 1) (R 1) [304,65,24,96,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b261
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 130, camps := [], pairs := [], upper := (rows 305 67 28 104 18 160 68 130 386), lower := (rows 305 67 28 104 18 160 68 128 256), losses := [] }

theorem u262 : Upper (D 1) (R 1) [304,65,24,96,2,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b262
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 279, targets := 128 }], pairs := [(0,7)], upper := (rows 305 67 28 104 18 160 192 134 262), lower := (rows 305 67 28 104 18 160 192 128 256), losses := [] }

theorem u263 : Upper (D 1) (R 1) [304,65,24,96,2,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b263
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 28 200 18 160 66 164 292), lower := (rows 305 67 28 200 18 160 66 128 256), losses := [] }

theorem u264 : Upper (D 1) (R 1) [304,65,24,192,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b264
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 28 200 18 160 68 162 290), lower := (rows 305 67 28 200 18 160 68 128 256), losses := [] }

theorem u265 : Upper (D 1) (R 1) [304,65,24,192,2,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b265
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 28 200 18 160 96 134 262), lower := (rows 305 67 28 200 18 160 96 128 256), losses := [] }

theorem u266 : Upper (D 1) (R 1) [304,65,24,192,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b266
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 76 152 18 160 66 164 292), lower := (rows 305 67 76 152 18 160 66 128 256), losses := [] }

theorem u267 : Upper (D 1) (R 1) [304,65,72,144,2,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b267
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 76 152 18 160 68 162 290), lower := (rows 305 67 76 152 18 160 68 128 256), losses := [] }

theorem u268 : Upper (D 1) (R 1) [304,65,72,144,2,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b268
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 6, camps := [{ cop := 1, region := 156, targets := 32 }], pairs := [(2,5)], upper := (rows 305 67 76 152 18 160 96 134 262), lower := (rows 305 67 76 152 18 160 96 128 256), losses := [] }

theorem u269 : Upper (D 1) (R 1) [304,65,72,144,2,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b269
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 305 67 84 138 144 34 68 168 296), lower := (rows 305 67 84 138 144 34 68 128 256), losses := [] }

theorem u270 : Upper (D 1) (R 1) [304,65,80,130,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b270
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 305 67 84 138 144 34 72 164 292), lower := (rows 305 67 84 138 144 34 72 128 256), losses := [] }

theorem u271 : Upper (D 1) (R 1) [304,65,80,130,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b271
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 67 84 138 144 34 96 140 268), lower := (rows 305 67 84 138 144 34 96 128 256), losses := [] }

theorem u272 : Upper (D 1) (R 1) [304,65,80,130,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b272
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 140 144 34 66 168 296), lower := (rows 305 67 84 140 144 34 66 128 256), losses := [] }

theorem u273 : Upper (D 1) (R 1) [304,65,80,132,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b273
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 67 84 140 144 34 72 162 290), lower := (rows 305 67 84 140 144 34 72 128 256), losses := [] }

theorem u274 : Upper (D 1) (R 1) [304,65,80,132,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b274
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 66, targets := 128 }], pairs := [(1,7)], upper := (rows 305 67 84 140 144 34 96 138 266), lower := (rows 305 67 84 140 144 34 96 128 256), losses := [] }

theorem u275 : Upper (D 1) (R 1) [304,65,80,132,128,2,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b275
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 67 84 168 144 34 66 140 268), lower := (rows 305 67 84 168 144 34 66 128 256), losses := [] }

theorem u276 : Upper (D 1) (R 1) [304,65,80,160,128,2,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b276
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 84 168 144 34 68 138 266), lower := (rows 305 67 84 168 144 34 68 128 256), losses := [] }

theorem u277 : Upper (D 1) (R 1) [304,65,80,160,128,2,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b277
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 84 168 144 34 72 134 262), lower := (rows 305 67 84 168 144 34 72 128 256), losses := [] }

theorem u278 : Upper (D 1) (R 1) [304,65,80,160,128,2,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b278
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 140, targets := 2 }], pairs := [(2,1)], upper := (rows 305 67 148 168 18 96 66 140 268), lower := (rows 305 67 148 168 18 96 66 128 256), losses := [] }

theorem u279 : Upper (D 1) (R 1) [304,65,144,160,2,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b279
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 67 148 168 18 96 68 138 266), lower := (rows 305 67 148 168 18 96 68 128 256), losses := [] }

theorem u280 : Upper (D 1) (R 1) [304,65,144,160,2,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b280
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 6, camps := [], pairs := [], upper := (rows 305 67 148 168 18 96 72 134 262), lower := (rows 305 67 148 168 18 96 72 128 256), losses := [] }

theorem u281 : Upper (D 1) (R 1) [304,65,144,160,2,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b281
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 7 152 80 160 66 168 296), lower := (rows 305 70 7 152 80 160 66 128 256), losses := [] }

theorem u282 : Upper (D 1) (R 1) [304,68,3,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b282
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 7 152 80 160 72 162 290), lower := (rows 305 70 7 152 80 160 72 128 256), losses := [] }

theorem u283 : Upper (D 1) (R 1) [304,68,3,144,64,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b283
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 7 152 80 160 96 138 266), lower := (rows 305 70 7 152 80 160 96 128 256), losses := [] }

theorem u284 : Upper (D 1) (R 1) [304,68,3,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b284
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 48, camps := [{ cop := 2, region := 66, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 13 138 80 160 66 176 304), lower := (rows 305 70 13 138 80 160 66 128 256), losses := [] }

theorem u285 : Upper (D 1) (R 1) [304,68,9,130,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b285
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 168, targets := 16 }], pairs := [(3,4)], upper := (rows 305 70 13 138 80 160 80 162 290), lower := (rows 305 70 13 138 80 160 80 128 256), losses := [] }

theorem u286 : Upper (D 1) (R 1) [304,68,9,130,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b286
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 18, camps := [{ cop := 1, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 305 70 13 138 80 160 96 146 274), lower := (rows 305 70 13 138 80 160 96 128 256), losses := [] }

theorem u287 : Upper (D 1) (R 1) [304,68,9,130,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b287
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 48, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 137 80 160 66 176 304), lower := (rows 305 70 14 137 80 160 66 128 256), losses := [] }

theorem u288 : Upper (D 1) (R 1) [304,68,10,129,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b288
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 86, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 137 80 160 80 162 290), lower := (rows 305 70 14 137 80 160 80 128 256), losses := [] }

theorem u289 : Upper (D 1) (R 1) [304,68,10,129,64,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b289
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 102, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 137 80 160 96 146 274), lower := (rows 305 70 14 137 80 160 96 128 256), losses := [] }

theorem u290 : Upper (D 1) (R 1) [304,68,10,129,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b290
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 14 152 80 160 65 162 290), lower := (rows 305 70 14 152 80 160 65 128 256), losses := [] }

theorem u291 : Upper (D 1) (R 1) [304,68,10,144,64,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b291
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 33, camps := [{ cop := 3, region := 70, targets := 32 }], pairs := [(1,5)], upper := (rows 305 70 14 152 80 160 66 161 289), lower := (rows 305 70 14 152 80 160 66 128 256), losses := [] }

theorem u292 : Upper (D 1) (R 1) [304,68,10,144,64,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b292
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 3, camps := [{ cop := 3, region := 102, targets := 16 }], pairs := [(1,4)], upper := (rows 305 70 14 152 80 160 96 131 259), lower := (rows 305 70 14 152 80 160 96 128 256), losses := [] }

theorem u293 : Upper (D 1) (R 1) [304,68,10,144,64,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b293
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 409, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 137 144 96 66 168 296), lower := (rows 305 70 22 137 144 96 66 128 256), losses := [] }

theorem u294 : Upper (D 1) (R 1) [304,68,18,129,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b294
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 34, camps := [], pairs := [], upper := (rows 305 70 22 137 144 96 72 162 290), lower := (rows 305 70 22 137 144 96 72 128 256), losses := [] }

theorem u295 : Upper (D 1) (R 1) [304,68,18,129,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b295
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 70, targets := 128 }], pairs := [(1,7)], upper := (rows 305 70 22 137 144 96 96 138 266), lower := (rows 305 70 22 137 144 96 96 128 256), losses := [] }

theorem u296 : Upper (D 1) (R 1) [304,68,18,129,128,64,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b296
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 10, camps := [], pairs := [], upper := (rows 305 70 22 168 144 96 65 138 266), lower := (rows 305 70 22 168 144 96 65 128 256), losses := [] }

theorem u297 : Upper (D 1) (R 1) [304,68,18,160,128,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b297
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 9, camps := [{ cop := 5, region := 409, targets := 2 }], pairs := [(0,1)], upper := (rows 305 70 22 168 144 96 66 137 265), lower := (rows 305 70 22 168 144 96 66 128 256), losses := [] }

theorem u298 : Upper (D 1) (R 1) [304,68,18,160,128,64,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b298
    (constants 1).1 (constants 1).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 305 70 22 168 144 96 72 131 259), lower := (rows 305 70 22 168 144 96 72 128 256), losses := [] }

theorem u299 : Upper (D 1) (R 1) [304,68,18,160,128,64,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 1) 14 b299
    (constants 1).1 (constants 1).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P01
