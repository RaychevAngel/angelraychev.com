import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P00
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b360 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 67 140 328 20 160 113 177 305), lower := (rows 51 67 140 328 20 160 64 128 256), losses := [] }

theorem u360 : Upper (D 0) (R 0) [50,65,136,320,4,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b360
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b361 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 140 328 48 160 85 149 277), lower := (rows 51 67 140 328 48 160 64 128 256), losses := [] }

theorem u361 : Upper (D 0) (R 0) [50,65,136,320,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b361
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b362 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 268 17 160 120 184 312), lower := (rows 51 67 196 268 17 160 64 128 256), losses := [] }

theorem u362 : Upper (D 0) (R 0) [50,65,192,260,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b362
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b363 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 67 196 268 24 160 113 177 305), lower := (rows 51 67 196 268 24 160 64 128 256), losses := [] }

theorem u363 : Upper (D 0) (R 0) [50,65,192,260,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b363
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b364 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 67 196 268 48 160 89 153 281), lower := (rows 51 67 196 268 48 160 64 128 256), losses := [] }

theorem u364 : Upper (D 0) (R 0) [50,65,192,260,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b364
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b365 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 460, targets := 1 }], pairs := [(2,0)], upper := (rows 51 67 196 280 144 33 108 172 300), lower := (rows 51 67 196 280 144 33 64 128 256), losses := [] }

theorem u365 : Upper (D 0) (R 0) [50,65,192,272,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b365
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b366 : PairBound 9 := { available := 41, camps := [], pairs := [], upper := (rows 51 67 196 280 144 36 105 169 297), lower := (rows 51 67 196 280 144 36 64 128 256), losses := [] }

theorem u366 : Upper (D 0) (R 0) [50,65,192,272,128,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b366
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b367 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 67 196 280 144 40 101 165 293), lower := (rows 51 67 196 280 144 40 64 128 256), losses := [] }

theorem u367 : Upper (D 0) (R 0) [50,65,192,272,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b367
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b368 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 261 88 144 33 232 168 424), lower := (rows 51 70 261 88 144 33 64 128 256), losses := [] }

theorem u368 : Upper (D 0) (R 0) [50,68,257,80,128,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b368
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b369 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 70 261 88 144 40 225 161 417), lower := (rows 51 70 261 88 144 40 64 128 256), losses := [] }

theorem u369 : Upper (D 0) (R 0) [50,68,257,80,128,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b369
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b370 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 334, targets := 128 }], pairs := [(1,7)], upper := (rows 51 70 261 88 144 160 105 169 297), lower := (rows 51 70 261 88 144 160 64 128 256), losses := [] }

theorem u370 : Upper (D 0) (R 0) [50,68,257,80,128,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b370
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b371 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 70 261 137 24 160 112 240 368), lower := (rows 51 70 261 137 24 160 64 128 256), losses := [] }

theorem u371 : Upper (D 0) (R 0) [50,68,257,129,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b371
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b372 : PairBound 9 := { available := 88, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 137 48 160 88 216 344), lower := (rows 51 70 261 137 48 160 64 128 256), losses := [] }

theorem u372 : Upper (D 0) (R 0) [50,68,257,129,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b372
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b373 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 261 137 80 160 120 184 312), lower := (rows 51 70 261 137 80 160 64 128 256), losses := [] }

theorem u373 : Upper (D 0) (R 0) [50,68,257,129,64,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b373
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b374 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 200, targets := 1 }], pairs := [(3,0)], upper := (rows 51 70 261 200 17 160 120 184 312), lower := (rows 51 70 261 200 17 160 64 128 256), losses := [] }

theorem u374 : Upper (D 0) (R 0) [50,68,257,192,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b374
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b375 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 70 261 200 24 160 113 177 305), lower := (rows 51 70 261 200 24 160 64 128 256), losses := [] }

theorem u375 : Upper (D 0) (R 0) [50,68,257,192,8,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b375
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b376 : PairBound 9 := { available := 25, camps := [{ cop := 0, region := 462, targets := 32 }], pairs := [(1,5)], upper := (rows 51 70 261 200 48 160 89 153 281), lower := (rows 51 70 261 200 48 160 64 128 256), losses := [] }

theorem u376 : Upper (D 0) (R 0) [50,68,257,192,32,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b376
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b377 : PairBound 9 := { available := 168, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 70 388 88 17 33 232 168 424), lower := (rows 51 70 388 88 17 33 64 128 256), losses := [] }

theorem u377 : Upper (D 0) (R 0) [50,68,384,80,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b377
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b378 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 70 388 88 17 40 225 161 417), lower := (rows 51 70 388 88 17 40 64 128 256), losses := [] }

theorem u378 : Upper (D 0) (R 0) [50,68,384,80,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b378
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b379 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 72, targets := 128 }], pairs := [(3,7)], upper := (rows 51 70 388 88 17 160 105 169 297), lower := (rows 51 70 388 88 17 160 64 128 256), losses := [] }

theorem u379 : Upper (D 0) (R 0) [50,68,384,80,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b379
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b380 : PairBound 9 := { available := 112, camps := [], pairs := [], upper := (rows 51 70 388 137 17 40 112 240 368), lower := (rows 51 70 388 137 17 40 64 128 256), losses := [] }

theorem u380 : Upper (D 0) (R 0) [50,68,384,129,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b380
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b381 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 137 17 48 104 232 360), lower := (rows 51 70 388 137 17 48 64 128 256), losses := [] }

theorem u381 : Upper (D 0) (R 0) [50,68,384,129,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b381
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b382 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 137 17 96 120 184 312), lower := (rows 51 70 388 137 17 96 64 128 256), losses := [] }

theorem u382 : Upper (D 0) (R 0) [50,68,384,129,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b382
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b383 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 70 388 152 17 33 104 232 360), lower := (rows 51 70 388 152 17 33 64 128 256), losses := [] }

theorem u383 : Upper (D 0) (R 0) [50,68,384,144,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b383
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b384 : PairBound 9 := { available := 97, camps := [], pairs := [], upper := (rows 51 70 388 152 17 40 97 225 353), lower := (rows 51 70 388 152 17 40 64 128 256), losses := [] }

theorem u384 : Upper (D 0) (R 0) [50,68,384,144,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b384
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b385 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 70 388 152 17 96 105 169 297), lower := (rows 51 70 388 152 17 96 64 128 256), losses := [] }

theorem u385 : Upper (D 0) (R 0) [50,68,384,144,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b385
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b386 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 70 388 200 17 33 120 184 312), lower := (rows 51 70 388 200 17 33 64 128 256), losses := [] }

theorem u386 : Upper (D 0) (R 0) [50,68,384,192,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b386
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b387 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 70 388 200 17 40 113 177 305), lower := (rows 51 70 388 200 17 40 64 128 256), losses := [] }

theorem u387 : Upper (D 0) (R 0) [50,68,384,192,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b387
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b388 : PairBound 9 := { available := 41, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 70 388 200 17 48 105 169 297), lower := (rows 51 70 388 200 17 48 64 128 256), losses := [] }

theorem u388 : Upper (D 0) (R 0) [50,68,384,192,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b388
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b389 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 194 13 328 17 36 240 176 432), lower := (rows 51 194 13 328 17 36 64 128 256), losses := [] }

theorem u389 : Upper (D 0) (R 0) [50,192,9,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b389
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b390 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 13 328 17 48 228 164 420), lower := (rows 51 194 13 328 17 48 64 128 256), losses := [] }

theorem u390 : Upper (D 0) (R 0) [50,192,9,320,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b390
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b391 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 13 328 17 160 116 180 308), lower := (rows 51 194 13 328 17 160 64 128 256), losses := [] }

theorem u391 : Upper (D 0) (R 0) [50,192,9,320,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b391
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b392 : PairBound 9 := { available := 388, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 28 104 17 33 452 388 388), lower := (rows 51 194 28 104 17 33 64 128 256), losses := [] }

theorem u392 : Upper (D 0) (R 0) [50,192,24,96,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b392
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b393 : PairBound 9 := { available := 385, camps := [], pairs := [], upper := (rows 51 194 28 104 17 36 449 385 385), lower := (rows 51 194 28 104 17 36 64 128 256), losses := [] }

theorem u393 : Upper (D 0) (R 0) [50,192,24,96,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b393
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b394 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 104 17 160 325 389 261), lower := (rows 51 194 28 104 17 160 64 128 256), losses := [] }

theorem u394 : Upper (D 0) (R 0) [50,192,24,96,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b394
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b395 : PairBound 9 := { available := 133, camps := [], pairs := [], upper := (rows 51 194 28 104 17 288 197 133 389), lower := (rows 51 194 28 104 17 288 64 128 256), losses := [] }

theorem u395 : Upper (D 0) (R 0) [50,192,24,96,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b395
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b396 : PairBound 9 := { available := 196, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 28 296 17 33 196 196 452), lower := (rows 51 194 28 296 17 33 64 128 256), losses := [] }

theorem u396 : Upper (D 0) (R 0) [50,192,24,288,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b396
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b397 : PairBound 9 := { available := 193, camps := [], pairs := [], upper := (rows 51 194 28 296 17 36 193 193 449), lower := (rows 51 194 28 296 17 36 64 128 256), losses := [] }

theorem u397 : Upper (D 0) (R 0) [50,192,24,288,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b397
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b398 : PairBound 9 := { available := 133, camps := [{ cop := 0, region := 396, targets := 64 }], pairs := [(2,6)], upper := (rows 51 194 28 296 17 96 197 133 389), lower := (rows 51 194 28 296 17 96 64 128 256), losses := [] }

theorem u398 : Upper (D 0) (R 0) [50,192,24,288,1,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b398
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b399 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 28 328 17 33 228 164 420), lower := (rows 51 194 28 328 17 33 64 128 256), losses := [] }

theorem u399 : Upper (D 0) (R 0) [50,192,24,320,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b399
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b400 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 28 328 17 36 225 161 417), lower := (rows 51 194 28 328 17 36 64 128 256), losses := [] }

theorem u400 : Upper (D 0) (R 0) [50,192,24,320,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b400
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b401 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 28 328 17 160 101 165 293), lower := (rows 51 194 28 328 17 160 64 128 256), losses := [] }

theorem u401 : Upper (D 0) (R 0) [50,192,24,320,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b401
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b402 : PairBound 9 := { available := 292, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 76 152 17 33 356 420 292), lower := (rows 51 194 76 152 17 33 64 128 256), losses := [] }

theorem u402 : Upper (D 0) (R 0) [50,192,72,144,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b402
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b403 : PairBound 9 := { available := 289, camps := [], pairs := [], upper := (rows 51 194 76 152 17 36 353 417 289), lower := (rows 51 194 76 152 17 36 64 128 256), losses := [] }

theorem u403 : Upper (D 0) (R 0) [50,192,72,144,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b403
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b404 : PairBound 9 := { available := 37, camps := [], pairs := [], upper := (rows 51 194 76 152 17 288 101 165 293), lower := (rows 51 194 76 152 17 288 64 128 256), losses := [] }

theorem u404 : Upper (D 0) (R 0) [50,192,72,144,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b404
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b405 : PairBound 9 := { available := 176, camps := [], pairs := [], upper := (rows 51 194 76 265 17 36 240 176 432), lower := (rows 51 194 76 265 17 36 64 128 256), losses := [] }

theorem u405 : Upper (D 0) (R 0) [50,192,72,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b405
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b406 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 265 17 48 228 164 420), lower := (rows 51 194 76 265 17 48 64 128 256), losses := [] }

theorem u406 : Upper (D 0) (R 0) [50,192,72,257,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b406
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b407 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 265 17 160 116 180 308), lower := (rows 51 194 76 265 17 160 64 128 256), losses := [] }

theorem u407 : Upper (D 0) (R 0) [50,192,72,257,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b407
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b408 : PairBound 9 := { available := 164, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 76 280 17 33 228 164 420), lower := (rows 51 194 76 280 17 33 64 128 256), losses := [] }

theorem u408 : Upper (D 0) (R 0) [50,192,72,272,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b408
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b409 : PairBound 9 := { available := 161, camps := [], pairs := [], upper := (rows 51 194 76 280 17 36 225 161 417), lower := (rows 51 194 76 280 17 36 64 128 256), losses := [] }

theorem u409 : Upper (D 0) (R 0) [50,192,72,272,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b409
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b410 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 332, targets := 128 }], pairs := [(2,7)], upper := (rows 51 194 76 280 17 160 101 165 293), lower := (rows 51 194 76 280 17 160 64 128 256), losses := [] }

theorem u410 : Upper (D 0) (R 0) [50,192,72,272,1,128] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b410
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b411 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 76 392 17 33 116 180 308), lower := (rows 51 194 76 392 17 33 64 128 256), losses := [] }

theorem u411 : Upper (D 0) (R 0) [50,192,72,384,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b411
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b412 : PairBound 9 := { available := 49, camps := [], pairs := [], upper := (rows 51 194 76 392 17 36 113 177 305), lower := (rows 51 194 76 392 17 36 64 128 256), losses := [] }

theorem u412 : Upper (D 0) (R 0) [50,192,72,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b412
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b413 : PairBound 9 := { available := 37, camps := [{ cop := 0, region := 462, targets := 16 }], pairs := [(1,4)], upper := (rows 51 194 76 392 17 48 101 165 293), lower := (rows 51 194 76 392 17 48 64 128 256), losses := [] }

theorem u413 : Upper (D 0) (R 0) [50,192,72,384,1,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b413
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b414 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 462, targets := 1 }], pairs := [(1,0)], upper := (rows 51 194 84 168 17 33 332 396 268), lower := (rows 51 194 84 168 17 33 64 128 256), losses := [] }

theorem u414 : Upper (D 0) (R 0) [50,192,80,160,1,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b414
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b415 : PairBound 9 := { available := 265, camps := [], pairs := [], upper := (rows 51 194 84 168 17 36 329 393 265), lower := (rows 51 194 84 168 17 36 64 128 256), losses := [] }

theorem u415 : Upper (D 0) (R 0) [50,192,80,160,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b415
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b416 : PairBound 9 := { available := 261, camps := [], pairs := [], upper := (rows 51 194 84 168 17 40 325 389 261), lower := (rows 51 194 84 168 17 40 64 128 256), losses := [] }

theorem u416 : Upper (D 0) (R 0) [50,192,80,160,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b416
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b417 : PairBound 9 := { available := 13, camps := [], pairs := [], upper := (rows 51 194 84 168 17 288 77 141 269), lower := (rows 51 194 84 168 17 288 64 128 256), losses := [] }

theorem u417 : Upper (D 0) (R 0) [50,192,80,160,1,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b417
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b418 : PairBound 9 := { available := 168, camps := [], pairs := [], upper := (rows 51 194 84 265 17 36 232 168 424), lower := (rows 51 194 84 265 17 36 64 128 256), losses := [] }

theorem u418 : Upper (D 0) (R 0) [50,192,80,257,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b418
    (constants 0).1 (constants 0).2 (by decide +kernel)

def b419 : PairBound 9 := { available := 164, camps := [], pairs := [], upper := (rows 51 194 84 265 17 40 228 164 420), lower := (rows 51 194 84 265 17 40 64 128 256), losses := [] }

theorem u419 : Upper (D 0) (R 0) [50,192,80,257,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 0) 14 b419
    (constants 0).1 (constants 0).2 (by decide +kernel)

#print axioms u419
end Delivery.IrregularNine14.P00
