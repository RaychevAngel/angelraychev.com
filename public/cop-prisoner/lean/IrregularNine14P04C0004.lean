import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P04
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b240 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 25 400 58 90 154 282), lower := (rows 7 7 100 25 400 32 64 128 256), losses := [] }

theorem u240 : Upper (D 4) (R 4) [6,5,96,17,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b240
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b241 : PairBound 9 := { available := 26, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 137 280 58 90 154 282), lower := (rows 7 7 100 137 280 32 64 128 256), losses := [] }

theorem u241 : Upper (D 4) (R 4) [6,5,96,129,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b241
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b242 : PairBound 9 := { available := 27, camps := [{ cop := 2, region := 3, targets := 8 }], pairs := [(0,3)], upper := (rows 7 7 100 152 280 59 91 155 283), lower := (rows 7 7 100 152 280 32 64 128 256), losses := [] }

theorem u242 : Upper (D 4) (R 4) [6,5,96,144,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b242
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b243 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 56 82 436 468 404 404), lower := (rows 7 11 13 56 82 32 64 128 256), losses := [] }

theorem u243 : Upper (D 4) (R 4) [6,9,9,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b243
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b244 : PairBound 9 := { available := 278, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 56 208 310 342 406 278), lower := (rows 7 11 13 56 208 32 64 128 256), losses := [] }

theorem u244 : Upper (D 4) (R 4) [6,9,9,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b244
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b245 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 104 146 308 340 404 276), lower := (rows 7 11 13 104 146 32 64 128 256), losses := [] }

theorem u245 : Upper (D 4) (R 4) [6,9,9,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b245
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b246 : PairBound 9 := { available := 22, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 13 104 400 54 86 150 278), lower := (rows 7 11 13 104 400 32 64 128 256), losses := [] }

theorem u246 : Upper (D 4) (R 4) [6,9,9,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b246
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b247 : PairBound 9 := { available := 404, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 56 81 436 468 404 404), lower := (rows 7 11 14 56 81 32 64 128 256), losses := [] }

theorem u247 : Upper (D 4) (R 4) [6,9,10,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b247
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b248 : PairBound 9 := { available := 277, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 56 208 309 341 405 277), lower := (rows 7 11 14 56 208 32 64 128 256), losses := [] }

theorem u248 : Upper (D 4) (R 4) [6,9,10,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b248
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b249 : PairBound 9 := { available := 276, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 104 145 308 340 404 276), lower := (rows 7 11 14 104 145 32 64 128 256), losses := [] }

theorem u249 : Upper (D 4) (R 4) [6,9,10,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b249
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b250 : PairBound 9 := { available := 21, camps := [{ cop := 3, region := 7, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 14 104 400 53 85 149 277), lower := (rows 7 11 14 104 400 32 64 128 256), losses := [] }

theorem u250 : Upper (D 4) (R 4) [6,9,10,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b250
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b251 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 44 88 434 466 402 402), lower := (rows 7 11 21 44 88 32 64 128 256), losses := [] }

theorem u251 : Upper (D 4) (R 4) [6,9,17,36,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b251
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b252 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 44 208 314 346 410 282), lower := (rows 7 11 21 44 208 32 64 128 256), losses := [] }

theorem u252 : Upper (D 4) (R 4) [6,9,17,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b252
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b253 : PairBound 9 := { available := 390, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 56 88 422 454 390 390), lower := (rows 7 11 21 56 88 32 64 128 256), losses := [] }

theorem u253 : Upper (D 4) (R 4) [6,9,17,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b253
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b254 : PairBound 9 := { available := 270, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 56 208 302 334 398 270), lower := (rows 7 11 21 56 208 32 64 128 256), losses := [] }

theorem u254 : Upper (D 4) (R 4) [6,9,17,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b254
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b255 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 21 104 400 62 94 158 286), lower := (rows 7 11 21 104 400 32 64 128 256), losses := [] }

theorem u255 : Upper (D 4) (R 4) [6,9,17,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b255
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b256 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 44 208 313 345 409 281), lower := (rows 7 11 22 44 208 32 64 128 256), losses := [] }

theorem u256 : Upper (D 4) (R 4) [6,9,18,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b256
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b257 : PairBound 9 := { available := 396, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 56 81 428 460 396 396), lower := (rows 7 11 22 56 81 32 64 128 256), losses := [] }

theorem u257 : Upper (D 4) (R 4) [6,9,18,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b257
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b258 : PairBound 9 := { available := 393, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 56 84 425 457 393 393), lower := (rows 7 11 22 56 84 32 64 128 256), losses := [] }

theorem u258 : Upper (D 4) (R 4) [6,9,18,48,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b258
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b259 : PairBound 9 := { available := 389, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 56 88 421 453 389 389), lower := (rows 7 11 22 56 88 32 64 128 256), losses := [] }

theorem u259 : Upper (D 4) (R 4) [6,9,18,48,72] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b259
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b260 : PairBound 9 := { available := 269, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 56 208 301 333 397 269), lower := (rows 7 11 22 56 208 32 64 128 256), losses := [] }

theorem u260 : Upper (D 4) (R 4) [6,9,18,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b260
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b261 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 104 145 316 348 412 284), lower := (rows 7 11 22 104 145 32 64 128 256), losses := [] }

theorem u261 : Upper (D 4) (R 4) [6,9,18,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b261
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b262 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 104 148 313 345 409 281), lower := (rows 7 11 22 104 148 32 64 128 256), losses := [] }

theorem u262 : Upper (D 4) (R 4) [6,9,18,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b262
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b263 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 104 152 309 341 405 277), lower := (rows 7 11 22 104 152 32 64 128 256), losses := [] }

theorem u263 : Upper (D 4) (R 4) [6,9,18,96,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b263
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b264 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 504, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 22 104 400 61 93 157 285), lower := (rows 7 11 22 104 400 32 64 128 256), losses := [] }

theorem u264 : Upper (D 4) (R 4) [6,9,18,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b264
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b265 : PairBound 9 := { available := 404, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 28 41 82 436 468 404 404), lower := (rows 7 11 28 41 82 32 64 128 256), losses := [] }

theorem u265 : Upper (D 4) (R 4) [6,9,24,33,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b265
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b266 : PairBound 9 := { available := 402, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 28 41 84 434 466 402 402), lower := (rows 7 11 28 41 84 32 64 128 256), losses := [] }

theorem u266 : Upper (D 4) (R 4) [6,9,24,33,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b266
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b267 : PairBound 9 := { available := 278, camps := [{ cop := 1, region := 468, targets := 1 }], pairs := [(2,0)], upper := (rows 7 11 28 41 208 310 342 406 278), lower := (rows 7 11 28 41 208 32 64 128 256), losses := [] }

theorem u267 : Upper (D 4) (R 4) [6,9,24,33,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b267
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b268 : PairBound 9 := { available := 404, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 28 42 81 436 468 404 404), lower := (rows 7 11 28 42 81 32 64 128 256), losses := [] }

theorem u268 : Upper (D 4) (R 4) [6,9,24,34,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b268
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b269 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 28 42 84 433 465 401 401), lower := (rows 7 11 28 42 84 32 64 128 256), losses := [] }

theorem u269 : Upper (D 4) (R 4) [6,9,24,34,68] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b269
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b270 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 464, targets := 2 }], pairs := [(4,1)], upper := (rows 7 11 28 42 208 309 341 405 277), lower := (rows 7 11 28 42 208 32 64 128 256), losses := [] }

theorem u270 : Upper (D 4) (R 4) [6,9,24,34,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b270
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b271 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 464, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 28 44 81 434 466 402 402), lower := (rows 7 11 28 44 81 32 64 128 256), losses := [] }

theorem u271 : Upper (D 4) (R 4) [6,9,24,36,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b271
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b272 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 464, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 28 44 82 433 465 401 401), lower := (rows 7 11 28 44 82 32 64 128 256), losses := [] }

theorem u272 : Upper (D 4) (R 4) [6,9,24,36,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b272
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b273 : PairBound 9 := { available := 275, camps := [{ cop := 0, region := 464, targets := 4 }], pairs := [(4,2)], upper := (rows 7 11 28 44 208 307 339 403 275), lower := (rows 7 11 28 44 208 32 64 128 256), losses := [] }

theorem u273 : Upper (D 4) (R 4) [6,9,24,36,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b273
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b274 : PairBound 9 := { available := 390, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 56 81 422 454 390 390), lower := (rows 7 11 28 56 81 32 64 128 256), losses := [] }

theorem u274 : Upper (D 4) (R 4) [6,9,24,48,65] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b274
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b275 : PairBound 9 := { available := 389, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 56 82 421 453 389 389), lower := (rows 7 11 28 56 82 32 64 128 256), losses := [] }

theorem u275 : Upper (D 4) (R 4) [6,9,24,48,66] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b275
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b276 : PairBound 9 := { available := 263, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 56 208 295 327 391 263), lower := (rows 7 11 28 56 208 32 64 128 256), losses := [] }

theorem u276 : Upper (D 4) (R 4) [6,9,24,48,192] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b276
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b277 : PairBound 9 := { available := 278, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 104 145 310 342 406 278), lower := (rows 7 11 28 104 145 32 64 128 256), losses := [] }

theorem u277 : Upper (D 4) (R 4) [6,9,24,96,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b277
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b278 : PairBound 9 := { available := 277, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 104 146 309 341 405 277), lower := (rows 7 11 28 104 146 32 64 128 256), losses := [] }

theorem u278 : Upper (D 4) (R 4) [6,9,24,96,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b278
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b279 : PairBound 9 := { available := 275, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 104 148 307 339 403 275), lower := (rows 7 11 28 104 148 32 64 128 256), losses := [] }

theorem u279 : Upper (D 4) (R 4) [6,9,24,96,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b279
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b280 : PairBound 9 := { available := 23, camps := [{ cop := 2, region := 3, targets := 16 }], pairs := [(0,4)], upper := (rows 7 11 28 104 400 55 87 151 279), lower := (rows 7 11 28 104 400 32 64 128 256), losses := [] }

theorem u280 : Upper (D 4) (R 4) [6,9,24,96,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b280
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b281 : PairBound 9 := { available := 400, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 74 28 432 464 400 400), lower := (rows 7 11 37 74 28 32 64 128 256), losses := [] }

theorem u281 : Upper (D 4) (R 4) [6,9,33,66,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b281
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b282 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 76 152 306 338 402 274), lower := (rows 7 11 37 76 152 32 64 128 256), losses := [] }

theorem u282 : Upper (D 4) (R 4) [6,9,33,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b282
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b283 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 76 400 58 90 154 282), lower := (rows 7 11 37 76 400 32 64 128 256), losses := [] }

theorem u283 : Upper (D 4) (R 4) [6,9,33,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b283
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b284 : PairBound 9 := { available := 402, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 28 434 466 402 402), lower := (rows 7 11 37 88 28 32 64 128 256), losses := [] }

theorem u284 : Upper (D 4) (R 4) [6,9,33,80,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b284
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b285 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 146 316 348 412 284), lower := (rows 7 11 37 88 146 32 64 128 256), losses := [] }

theorem u285 : Upper (D 4) (R 4) [6,9,33,80,130] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b285
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b286 : PairBound 9 := { available := 282, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 148 314 346 410 282), lower := (rows 7 11 37 88 148 32 64 128 256), losses := [] }

theorem u286 : Upper (D 4) (R 4) [6,9,33,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b286
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b287 : PairBound 9 := { available := 278, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 152 310 342 406 278), lower := (rows 7 11 37 88 152 32 64 128 256), losses := [] }

theorem u287 : Upper (D 4) (R 4) [6,9,33,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b287
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b288 : PairBound 9 := { available := 30, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 88 400 62 94 158 286), lower := (rows 7 11 37 88 400 32 64 128 256), losses := [] }

theorem u288 : Upper (D 4) (R 4) [6,9,33,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b288
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b289 : PairBound 9 := { available := 274, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 28 306 338 402 274), lower := (rows 7 11 37 200 28 32 64 128 256), losses := [] }

theorem u289 : Upper (D 4) (R 4) [6,9,33,192,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b289
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b290 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 274 60 92 156 284), lower := (rows 7 11 37 200 274 32 64 128 256), losses := [] }

theorem u290 : Upper (D 4) (R 4) [6,9,33,192,258] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b290
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b291 : PairBound 9 := { available := 26, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 276 58 90 154 282), lower := (rows 7 11 37 200 276 32 64 128 256), losses := [] }

theorem u291 : Upper (D 4) (R 4) [6,9,33,192,260] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b291
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b292 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 472, targets := 1 }], pairs := [(3,0)], upper := (rows 7 11 37 200 280 54 86 150 278), lower := (rows 7 11 37 200 280 32 64 128 256), losses := [] }

theorem u292 : Upper (D 4) (R 4) [6,9,33,192,264] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b292
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b293 : PairBound 9 := { available := 273, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 76 152 305 337 401 273), lower := (rows 7 11 38 76 152 32 64 128 256), losses := [] }

theorem u293 : Upper (D 4) (R 4) [6,9,34,68,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b293
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b294 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 76 400 57 89 153 281), lower := (rows 7 11 38 76 400 32 64 128 256), losses := [] }

theorem u294 : Upper (D 4) (R 4) [6,9,34,68,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b294
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b295 : PairBound 9 := { available := 401, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 28 433 465 401 401), lower := (rows 7 11 38 88 28 32 64 128 256), losses := [] }

theorem u295 : Upper (D 4) (R 4) [6,9,34,80,12] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b295
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b296 : PairBound 9 := { available := 284, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 145 316 348 412 284), lower := (rows 7 11 38 88 145 32 64 128 256), losses := [] }

theorem u296 : Upper (D 4) (R 4) [6,9,34,80,129] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b296
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b297 : PairBound 9 := { available := 281, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 148 313 345 409 281), lower := (rows 7 11 38 88 148 32 64 128 256), losses := [] }

theorem u297 : Upper (D 4) (R 4) [6,9,34,80,132] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b297
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b298 : PairBound 9 := { available := 277, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 152 309 341 405 277), lower := (rows 7 11 38 88 152 32 64 128 256), losses := [] }

theorem u298 : Upper (D 4) (R 4) [6,9,34,80,136] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b298
    (constants 4).1 (constants 4).2 (by decide +kernel)

def b299 : PairBound 9 := { available := 29, camps := [{ cop := 0, region := 472, targets := 2 }], pairs := [(3,1)], upper := (rows 7 11 38 88 400 61 93 157 285), lower := (rows 7 11 38 88 400 32 64 128 256), losses := [] }

theorem u299 : Upper (D 4) (R 4) [6,9,34,80,384] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 4) 14 b299
    (constants 4).1 (constants 4).2 (by decide +kernel)

#print axioms u299
end Delivery.IrregularNine14.P04
