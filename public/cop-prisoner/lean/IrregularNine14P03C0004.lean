import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P03
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 132, camps := [{ cop := 8, region := 99, targets := 128 }], pairs := [(0,7)], upper := (rows 35 259 28 73 176 96 65 132 388), lower := (rows 35 259 28 73 176 96 65 128 256), losses := [] }

theorem u240 : Upper (D 3) (R 3) [34,257,24,65,160,64,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b240
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 35 259 28 73 176 96 68 129 385), lower := (rows 35 259 28 73 176 96 68 128 256), losses := [] }

theorem u241 : Upper (D 3) (R 3) [34,257,24,65,160,64,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b241
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 5, camps := [{ cop := 6, region := 48, targets := 1 }], pairs := [(4,0)], upper := (rows 35 259 28 73 176 96 192 133 261), lower := (rows 35 259 28 73 176 96 192 128 256), losses := [] }

theorem u242 : Upper (D 3) (R 3) [34,257,24,65,160,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b242
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 80, camps := [], pairs := [], upper := (rows 35 259 44 73 145 160 68 208 336), lower := (rows 35 259 44 73 145 160 68 128 256), losses := [] }

theorem u243 : Upper (D 3) (R 3) [34,257,40,65,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b243
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 68, camps := [], pairs := [], upper := (rows 35 259 44 73 145 160 80 196 324), lower := (rows 35 259 44 73 145 160 80 128 256), losses := [] }

theorem u244 : Upper (D 3) (R 3) [34,257,40,65,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b244
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 80, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 259 44 73 148 160 65 208 336), lower := (rows 35 259 44 73 148 160 65 128 256), losses := [] }

theorem u245 : Upper (D 3) (R 3) [34,257,40,65,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b245
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 35 259 44 73 148 160 80 193 321), lower := (rows 35 259 44 73 148 160 80 128 256), losses := [] }

theorem u246 : Upper (D 3) (R 3) [34,257,40,65,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b246
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 76, targets := 128 }], pairs := [(2,7)], upper := (rows 35 259 44 73 208 160 65 148 276), lower := (rows 35 259 44 73 208 160 65 128 256), losses := [] }

theorem u247 : Upper (D 3) (R 3) [34,257,40,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b247
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 259 44 73 208 160 68 145 273), lower := (rows 35 259 44 73 208 160 68 128 256), losses := [] }

theorem u248 : Upper (D 3) (R 3) [34,257,40,65,192,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b248
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 259 44 73 208 160 80 133 261), lower := (rows 35 259 44 73 208 160 80 128 256), losses := [] }

theorem u249 : Upper (D 3) (R 3) [34,257,40,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b249
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 40, camps := [], pairs := [], upper := (rows 35 259 69 88 145 160 68 168 296), lower := (rows 35 259 69 88 145 160 68 128 256), losses := [] }

theorem u250 : Upper (D 3) (R 3) [34,257,65,80,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b250
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 36, camps := [], pairs := [], upper := (rows 35 259 69 88 145 160 72 164 292), lower := (rows 35 259 69 88 145 160 72 128 256), losses := [] }

theorem u251 : Upper (D 3) (R 3) [34,257,65,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b251
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 12, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5)], upper := (rows 35 259 69 88 145 160 96 140 268), lower := (rows 35 259 69 88 145 160 96 128 256), losses := [] }

theorem u252 : Upper (D 3) (R 3) [34,257,65,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b252
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 24, camps := [], pairs := [], upper := (rows 35 259 69 104 145 160 68 152 280), lower := (rows 35 259 69 104 145 160 68 128 256), losses := [] }

theorem u253 : Upper (D 3) (R 3) [34,257,65,96,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b253
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 20, camps := [], pairs := [], upper := (rows 35 259 69 104 145 160 72 148 276), lower := (rows 35 259 69 104 145 160 72 128 256), losses := [] }

theorem u254 : Upper (D 3) (R 3) [34,257,65,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b254
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 12, camps := [], pairs := [], upper := (rows 35 259 69 104 145 160 80 140 268), lower := (rows 35 259 69 104 145 160 80 128 256), losses := [] }

theorem u255 : Upper (D 3) (R 3) [34,257,65,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b255
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 259 69 104 148 160 65 152 280), lower := (rows 35 259 69 104 148 160 65 128 256), losses := [] }

theorem u256 : Upper (D 3) (R 3) [34,257,65,96,132,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b256
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 259 69 104 148 160 72 145 273), lower := (rows 35 259 69 104 148 160 72 128 256), losses := [] }

theorem u257 : Upper (D 3) (R 3) [34,257,65,96,132,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b257
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 259 69 104 148 160 80 137 265), lower := (rows 35 259 69 104 148 160 80 128 256), losses := [] }

theorem u258 : Upper (D 3) (R 3) [34,257,65,96,132,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b258
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 20, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 259 69 104 152 160 65 148 276), lower := (rows 35 259 69 104 152 160 65 128 256), losses := [] }

theorem u259 : Upper (D 3) (R 3) [34,257,65,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b259
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 259 69 104 152 160 68 145 273), lower := (rows 35 259 69 104 152 160 68 128 256), losses := [] }

theorem u260 : Upper (D 3) (R 3) [34,257,65,96,136,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b260
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 5, camps := [], pairs := [], upper := (rows 35 259 69 104 152 160 80 133 261), lower := (rows 35 259 69 104 152 160 80 128 256), losses := [] }

theorem u261 : Upper (D 3) (R 3) [34,257,65,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b261
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 69 25 208 160 65 168 296), lower := (rows 35 262 69 25 208 160 65 128 256), losses := [] }

theorem u262 : Upper (D 3) (R 3) [34,260,65,17,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b262
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 69 25 208 160 72 161 289), lower := (rows 35 262 69 25 208 160 72 128 256), losses := [] }

theorem u263 : Upper (D 3) (R 3) [34,260,65,17,192,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b263
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 25 208 160 96 137 265), lower := (rows 35 262 69 25 208 160 96 128 256), losses := [] }

theorem u264 : Upper (D 3) (R 3) [34,260,65,17,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b264
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 40, camps := [{ cop := 4, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 35 262 69 88 145 160 65 168 296), lower := (rows 35 262 69 88 145 160 65 128 256), losses := [] }

theorem u265 : Upper (D 3) (R 3) [34,260,65,80,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b265
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 35 262 69 88 145 160 72 161 289), lower := (rows 35 262 69 88 145 160 72 128 256), losses := [] }

theorem u266 : Upper (D 3) (R 3) [34,260,65,80,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b266
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 9, camps := [{ cop := 2, region := 410, targets := 32 }], pairs := [(1,5)], upper := (rows 35 262 69 88 145 160 96 137 265), lower := (rows 35 262 69 88 145 160 96 128 256), losses := [] }

theorem u267 : Upper (D 3) (R 3) [34,260,65,80,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b267
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 24, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 69 104 145 160 65 152 280), lower := (rows 35 262 69 104 145 160 65 128 256), losses := [] }

theorem u268 : Upper (D 3) (R 3) [34,260,65,96,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b268
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 35 262 69 104 145 160 72 145 273), lower := (rows 35 262 69 104 145 160 72 128 256), losses := [] }

theorem u269 : Upper (D 3) (R 3) [34,260,65,96,129,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b269
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 9, camps := [], pairs := [], upper := (rows 35 262 69 104 145 160 80 137 265), lower := (rows 35 262 69 104 145 160 80 128 256), losses := [] }

theorem u270 : Upper (D 3) (R 3) [34,260,65,96,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b270
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 68, targets := 128 }], pairs := [(2,7)], upper := (rows 35 262 69 104 152 160 65 145 273), lower := (rows 35 262 69 104 152 160 65 128 256), losses := [] }

theorem u271 : Upper (D 3) (R 3) [34,260,65,96,136,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b271
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 262 69 104 152 160 80 129 257), lower := (rows 35 262 69 104 152 160 80 128 256), losses := [] }

theorem u272 : Upper (D 3) (R 3) [34,260,65,96,136,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b272
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 35 322 28 104 145 160 65 133 261), lower := (rows 35 322 28 104 145 160 65 128 256), losses := [] }

theorem u273 : Upper (D 3) (R 3) [34,320,24,96,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b273
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 35 322 28 104 145 160 68 129 257), lower := (rows 35 322 28 104 145 160 68 128 256), losses := [] }

theorem u274 : Upper (D 3) (R 3) [34,320,24,96,129,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b274
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 97 7 28 137 273 34 192 224 352), lower := (rows 97 7 28 137 273 34 192 128 256), losses := [] }

theorem u275 : Upper (D 3) (R 3) [96,5,24,129,257,2,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b275
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 414, targets := 64 }], pairs := [(1,6)], upper := (rows 97 7 28 137 273 96 192 162 290), lower := (rows 97 7 28 137 273 96 192 128 256), losses := [] }

theorem u276 : Upper (D 3) (R 3) [96,5,24,129,257,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b276
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 66, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 273 160 65 194 322), lower := (rows 97 14 52 137 273 160 65 128 256), losses := [] }

theorem u277 : Upper (D 3) (R 3) [96,12,48,129,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b277
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 65, camps := [], pairs := [], upper := (rows 97 14 52 137 273 160 66 193 321), lower := (rows 97 14 52 137 273 160 66 128 256), losses := [] }

theorem u278 : Upper (D 3) (R 3) [96,12,48,129,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b278
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 137 336 160 65 131 259), lower := (rows 97 14 52 137 336 160 65 128 256), losses := [] }

theorem u279 : Upper (D 3) (R 3) [96,12,48,129,320,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b279
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 97 14 52 137 336 160 66 129 257), lower := (rows 97 14 52 137 336 160 66 128 256), losses := [] }

theorem u280 : Upper (D 3) (R 3) [96,12,48,129,320,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b280
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 3, camps := [{ cop := 2, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 52 200 273 160 65 131 259), lower := (rows 97 14 52 200 273 160 65 128 256), losses := [] }

theorem u281 : Upper (D 3) (R 3) [96,12,48,192,257,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b281
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 97 14 52 200 273 160 66 129 257), lower := (rows 97 14 52 200 273 160 66 128 256), losses := [] }

theorem u282 : Upper (D 3) (R 3) [96,12,48,192,257,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b282
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 65, targets := 128 }], pairs := [(0,7)], upper := (rows 97 14 133 296 82 160 65 145 273), lower := (rows 97 14 133 296 82 160 65 128 256), losses := [] }

theorem u283 : Upper (D 3) (R 3) [96,12,129,288,66,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b283
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 97 14 133 296 82 160 80 129 257), lower := (rows 97 14 133 296 82 160 80 128 256), losses := [] }

theorem u284 : Upper (D 3) (R 3) [96,12,129,288,66,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b284
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 18, camps := [{ cop := 3, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 97 38 76 265 145 160 65 146 274), lower := (rows 97 38 76 265 145 160 65 128 256), losses := [] }

theorem u285 : Upper (D 3) (R 3) [96,36,72,257,129,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b285
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 17, camps := [], pairs := [], upper := (rows 97 38 76 265 145 160 66 145 273), lower := (rows 97 38 76 265 145 160 66 128 256), losses := [] }

theorem u286 : Upper (D 3) (R 3) [96,36,72,257,129,128,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b286
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 3, camps := [], pairs := [], upper := (rows 97 38 76 265 145 160 80 131 259), lower := (rows 97 38 76 265 145 160 80 128 256), losses := [] }

theorem u287 : Upper (D 3) (R 3) [96,36,72,257,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b287
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 68, targets := 32 }], pairs := [(2,5)], upper := (rows 97 38 76 265 146 160 65 145 273), lower := (rows 97 38 76 265 146 160 65 128 256), losses := [] }

theorem u288 : Upper (D 3) (R 3) [96,36,72,257,130,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b288
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 1, camps := [], pairs := [], upper := (rows 97 38 76 265 146 160 80 129 257), lower := (rows 97 38 76 265 146 160 80 128 256), losses := [] }

theorem u289 : Upper (D 3) (R 3) [96,36,72,257,130,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b289
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 160, camps := [{ cop := 4, region := 46, targets := 128 }], pairs := [(1,7)], upper := (rows 259 7 28 41 81 96 192 160 416), lower := (rows 259 7 28 41 81 96 192 128 256), losses := [] }

theorem u290 : Upper (D 3) (R 3) [258,5,24,33,65,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b290
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 96, camps := [], pairs := [(1,5)], upper := (rows 259 7 28 41 81 160 192 224 352), lower := (rows 259 7 28 41 81 160 192 128 256), losses := [{ target := 5, region := (rows 1 10 12 8 24 0 224 128 256), good := (rows 259 7 30 95 81 192 192 192 256) }] }

theorem u291 : Upper (D 3) (R 3) [258,5,24,33,65,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b291
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 144, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 44 73 112 160 65 144 400), lower := (rows 259 7 44 73 112 160 65 128 256), losses := [] }

theorem u292 : Upper (D 3) (R 3) [258,5,40,65,96,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b292
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 129, camps := [], pairs := [], upper := (rows 259 7 44 73 112 160 80 129 385), lower := (rows 259 7 44 73 112 160 80 128 256), losses := [] }

theorem u293 : Upper (D 3) (R 3) [258,5,40,65,96,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b293
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 17, camps := [{ cop := 4, region := 271, targets := 128 }], pairs := [(0,7)], upper := (rows 259 7 44 73 112 160 192 145 273), lower := (rows 259 7 44 73 112 160 192 128 256), losses := [] }

theorem u294 : Upper (D 3) (R 3) [258,5,40,65,96,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b294
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 96, camps := [], pairs := [], upper := (rows 259 7 44 73 145 160 80 224 352), lower := (rows 259 7 44 73 145 160 80 128 256), losses := [] }

theorem u295 : Upper (D 3) (R 3) [258,5,40,65,129,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b295
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 80, camps := [{ cop := 3, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 44 73 145 160 96 208 336), lower := (rows 259 7 44 73 145 160 96 128 256), losses := [] }

theorem u296 : Upper (D 3) (R 3) [258,5,40,65,129,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b296
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 72, targets := 32 }], pairs := [(3,5)], upper := (rows 259 7 44 73 208 160 65 176 304), lower := (rows 259 7 44 73 208 160 65 128 256), losses := [] }

theorem u297 : Upper (D 3) (R 3) [258,5,40,65,192,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b297
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 33, camps := [], pairs := [], upper := (rows 259 7 44 73 208 160 80 161 289), lower := (rows 259 7 44 73 208 160 80 128 256), losses := [] }

theorem u298 : Upper (D 3) (R 3) [258,5,40,65,192,128,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b298
    (constants 3).1 (constants 3).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 17, camps := [{ cop := 3, region := 144, targets := 32 }], pairs := [(4,5)], upper := (rows 259 7 44 73 208 160 96 145 273), lower := (rows 259 7 44 73 208 160 96 128 256), losses := [] }

theorem u299 : Upper (D 3) (R 3) [258,5,40,65,192,128,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 3) 14 b299
    (constants 3).1 (constants 3).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P03
