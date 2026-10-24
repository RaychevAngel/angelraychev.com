import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting
import IrregularNine14P06C0016

namespace Delivery.IrregularNine14.P06
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b9360 : PairBound 9 := { available := 328, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 56 148 34 328 456 328), lower := (rows 7 35 69 56 148 34 64 128 256), losses := [] }

theorem u9360 : Upper (D 6) (R 6) [6,33,65,48,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9360
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9361 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 325, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 69 56 148 40 322 450 322), lower := (rows 7 35 69 56 148 40 64 128 256), losses := [] }

theorem u9361 : Upper (D 6) (R 6) [6,33,65,48,132,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9361
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9362 : PairBound 9 := { available := 266, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 56 148 96 330 394 266), lower := (rows 7 35 69 56 148 96 64 128 256), losses := [] }

theorem u9362 : Upper (D 6) (R 6) [6,33,65,48,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9362
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9363 : PairBound 9 := { available := 74, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 56 148 288 74 202 330), lower := (rows 7 35 69 56 148 288 64 128 256), losses := [] }

theorem u9363 : Upper (D 6) (R 6) [6,33,65,48,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9363
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9364 : PairBound 9 := { available := 268, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 56 208 34 332 396 268), lower := (rows 7 35 69 56 208 34 64 128 256), losses := [] }

theorem u9364 : Upper (D 6) (R 6) [6,33,65,48,192,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9364
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9365 : PairBound 9 := { available := 266, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 56 208 36 330 394 266), lower := (rows 7 35 69 56 208 36 64 128 256), losses := [] }

theorem u9365 : Upper (D 6) (R 6) [6,33,65,48,192,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9365
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9366 : PairBound 9 := { available := 262, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 69 56 208 40 326 390 262), lower := (rows 7 35 69 56 208 40 64 128 256), losses := [] }

theorem u9366 : Upper (D 6) (R 6) [6,33,65,48,192,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9366
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9367 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 56 208 288 78 142 270), lower := (rows 7 35 69 56 208 288 64 128 256), losses := [] }

theorem u9367 : Upper (D 6) (R 6) [6,33,65,48,192,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9367
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9368 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 56 400 34 76 204 332), lower := (rows 7 35 69 56 400 34 64 128 256), losses := [] }

theorem u9368 : Upper (D 6) (R 6) [6,33,65,48,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9368
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9369 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 56 400 36 74 202 330), lower := (rows 7 35 69 56 400 36 64 128 256), losses := [] }

theorem u9369 : Upper (D 6) (R 6) [6,33,65,48,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9369
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9370 : PairBound 9 := { available := 70, camps := [{ cop := 4, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 69 56 400 40 70 198 326), lower := (rows 7 35 69 56 400 40 64 128 256), losses := [] }

theorem u9370 : Upper (D 6) (R 6) [6,33,65,48,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9370
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9371 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 56 400 96 78 142 270), lower := (rows 7 35 69 56 400 96 64 128 256), losses := [] }

theorem u9371 : Upper (D 6) (R 6) [6,33,65,48,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9371
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9372 : PairBound 9 := { available := 280, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 104 146 36 344 408 280), lower := (rows 7 35 69 104 146 36 64 128 256), losses := [] }

theorem u9372 : Upper (D 6) (R 6) [6,33,65,96,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9372
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9373 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 69 104 146 40 340 404 276), lower := (rows 7 35 69 104 146 40 64 128 256), losses := [] }

theorem u9373 : Upper (D 6) (R 6) [6,33,65,96,130,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9373
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9374 : PairBound 9 := { available := 268, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 104 146 48 332 396 268), lower := (rows 7 35 69 104 146 48 64 128 256), losses := [] }

theorem u9374 : Upper (D 6) (R 6) [6,33,65,96,130,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9374
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9375 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 104 146 288 92 156 284), lower := (rows 7 35 69 104 146 288 64 128 256), losses := [] }

theorem u9375 : Upper (D 6) (R 6) [6,33,65,96,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9375
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9376 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 104 152 34 340 404 276), lower := (rows 7 35 69 104 152 34 64 128 256), losses := [] }

theorem u9376 : Upper (D 6) (R 6) [6,33,65,96,136,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9376
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9377 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 104 152 36 338 402 274), lower := (rows 7 35 69 104 152 36 64 128 256), losses := [] }

theorem u9377 : Upper (D 6) (R 6) [6,33,65,96,136,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9377
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9378 : PairBound 9 := { available := 262, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 104 152 48 326 390 262), lower := (rows 7 35 69 104 152 48 64 128 256), losses := [] }

theorem u9378 : Upper (D 6) (R 6) [6,33,65,96,136,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9378
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9379 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 104 152 288 86 150 278), lower := (rows 7 35 69 104 152 288 64 128 256), losses := [] }

theorem u9379 : Upper (D 6) (R 6) [6,33,65,96,136,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9379
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9380 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 104 400 34 92 156 284), lower := (rows 7 35 69 104 400 34 64 128 256), losses := [] }

theorem u9380 : Upper (D 6) (R 6) [6,33,65,96,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9380
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9381 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 104 400 36 90 154 282), lower := (rows 7 35 69 104 400 36 64 128 256), losses := [] }

theorem u9381 : Upper (D 6) (R 6) [6,33,65,96,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9381
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9382 : PairBound 9 := { available := 22, camps := [{ cop := 1, region := 469, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 69 104 400 40 86 150 278), lower := (rows 7 35 69 104 400 40 64 128 256), losses := [] }

theorem u9382 : Upper (D 6) (R 6) [6,33,65,96,384,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9382
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9383 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 104 400 48 78 142 270), lower := (rows 7 35 69 104 400 48 64 128 256), losses := [] }

theorem u9383 : Upper (D 6) (R 6) [6,33,65,96,384,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9383
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9384 : PairBound 9 := { available := 112, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 276 40 112 240 368), lower := (rows 7 35 69 138 276 40 64 128 256), losses := [] }

theorem u9384 : Upper (D 6) (R 6) [6,33,65,130,260,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9384
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9385 : PairBound 9 := { available := 104, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 276 48 104 232 360), lower := (rows 7 35 69 138 276 48 64 128 256), losses := [] }

theorem u9385 : Upper (D 6) (R 6) [6,33,65,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9385
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9386 : PairBound 9 := { available := 56, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 138 276 96 120 184 312), lower := (rows 7 35 69 138 276 96 64 128 256), losses := [] }

theorem u9386 : Upper (D 6) (R 6) [6,33,65,130,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9386
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9387 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 138 280 36 112 240 368), lower := (rows 7 35 69 138 280 36 64 128 256), losses := [] }

theorem u9387 : Upper (D 6) (R 6) [6,33,65,130,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9387
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9388 : PairBound 9 := { available := 100, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 280 48 100 228 356), lower := (rows 7 35 69 138 280 48 64 128 256), losses := [] }

theorem u9388 : Upper (D 6) (R 6) [6,33,65,130,264,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9388
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9389 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 138 280 96 116 180 308), lower := (rows 7 35 69 138 280 96 64 128 256), losses := [] }

theorem u9389 : Upper (D 6) (R 6) [6,33,65,130,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9389
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9390 : PairBound 9 := { available := 88, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 138 304 36 88 216 344), lower := (rows 7 35 69 138 304 36 64 128 256), losses := [] }

theorem u9390 : Upper (D 6) (R 6) [6,33,65,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9390
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9391 : PairBound 9 := { available := 84, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 304 40 84 212 340), lower := (rows 7 35 69 138 304 40 64 128 256), losses := [] }

theorem u9391 : Upper (D 6) (R 6) [6,33,65,130,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9391
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9392 : PairBound 9 := { available := 76, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 69 138 304 48 76 204 332), lower := (rows 7 35 69 138 304 48 64 128 256), losses := [] }

theorem u9392 : Upper (D 6) (R 6) [6,33,65,130,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9392
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9393 : PairBound 9 := { available := 28, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 138 304 96 92 156 284), lower := (rows 7 35 69 138 304 96 64 128 256), losses := [] }

theorem u9393 : Upper (D 6) (R 6) [6,33,65,130,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9393
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9394 : PairBound 9 := { available := 56, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 138 336 36 120 184 312), lower := (rows 7 35 69 138 336 36 64 128 256), losses := [] }

theorem u9394 : Upper (D 6) (R 6) [6,33,65,130,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9394
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9395 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 336 40 116 180 308), lower := (rows 7 35 69 138 336 40 64 128 256), losses := [] }

theorem u9395 : Upper (D 6) (R 6) [6,33,65,130,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9395
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9396 : PairBound 9 := { available := 44, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 138 336 48 108 172 300), lower := (rows 7 35 69 138 336 48 64 128 256), losses := [] }

theorem u9396 : Upper (D 6) (R 6) [6,33,65,130,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9396
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9397 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 152 280 34 100 228 356), lower := (rows 7 35 69 152 280 34 64 128 256), losses := [] }

theorem u9397 : Upper (D 6) (R 6) [6,33,65,144,264,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9397
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9398 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 152 280 36 98 226 354), lower := (rows 7 35 69 152 280 36 64 128 256), losses := [] }

theorem u9398 : Upper (D 6) (R 6) [6,33,65,144,264,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9398
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9399 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 152 280 96 102 166 294), lower := (rows 7 35 69 152 280 96 64 128 256), losses := [] }

theorem u9399 : Upper (D 6) (R 6) [6,33,65,144,264,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9399
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9400 : PairBound 9 := { available := 76, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 152 304 34 76 204 332), lower := (rows 7 35 69 152 304 34 64 128 256), losses := [] }

theorem u9400 : Upper (D 6) (R 6) [6,33,65,144,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9400
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9401 : PairBound 9 := { available := 74, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 152 304 36 74 202 330), lower := (rows 7 35 69 152 304 36 64 128 256), losses := [] }

theorem u9401 : Upper (D 6) (R 6) [6,33,65,144,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9401
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9402 : PairBound 9 := { available := 70, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 152 304 40 70 198 326), lower := (rows 7 35 69 152 304 40 64 128 256), losses := [] }

theorem u9402 : Upper (D 6) (R 6) [6,33,65,144,288,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9402
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9403 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 504, targets := 1 },{ cop := 2, region := 34, targets := 4 }], pairs := [(1,2),(3,0),(4,0)], upper := (rows 7 35 69 152 304 96 78 142 270), lower := (rows 7 35 69 152 304 96 64 128 256), losses := [] }

theorem u9403 : Upper (D 6) (R 6) [6,33,65,144,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9403
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9404 : PairBound 9 := { available := 28, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 69 168 336 34 92 156 284), lower := (rows 7 35 69 168 336 34 64 128 256), losses := [] }

theorem u9404 : Upper (D 6) (R 6) [6,33,65,160,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9404
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9405 : PairBound 9 := { available := 26, camps := [{ cop := 1, region := 472, targets := 5 }], pairs := [(3,0),(3,2),(4,0)], upper := (rows 7 35 69 168 336 36 90 154 282), lower := (rows 7 35 69 168 336 36 64 128 256), losses := [] }

theorem u9405 : Upper (D 6) (R 6) [6,33,65,160,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9405
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9406 : PairBound 9 := { available := 22, camps := [{ cop := 7, region := 40, targets := 3 }], pairs := [(3,0),(3,1)], upper := (rows 7 35 69 168 336 40 86 150 278), lower := (rows 7 35 69 168 336 40 64 128 256), losses := [] }

theorem u9406 : Upper (D 6) (R 6) [6,33,65,160,320,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9406
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9407 : PairBound 9 := { available := 14, camps := [{ cop := 0, region := 504, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 69 168 336 48 78 142 270), lower := (rows 7 35 69 168 336 48 64 128 256), losses := [] }

theorem u9407 : Upper (D 6) (R 6) [6,33,65,160,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9407
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9408 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 25 400 34 100 228 356), lower := (rows 7 35 76 25 400 34 64 128 256), losses := [] }

theorem u9408 : Upper (D 6) (R 6) [6,33,72,17,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9408
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9409 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 25 400 36 98 226 354), lower := (rows 7 35 76 25 400 36 64 128 256), losses := [] }

theorem u9409 : Upper (D 6) (R 6) [6,33,72,17,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9409
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9410 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 496, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 76 25 400 96 102 166 294), lower := (rows 7 35 76 25 400 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 111 65 129 257), good := (rows 502 498 124 508 400 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 27 400 96 96 128 256) }] }

theorem u9410 : Upper (D 6) (R 6) [6,33,72,17,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9410
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9411 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 26 400 33 100 228 356), lower := (rows 7 35 76 26 400 33 64 128 256), losses := [] }

theorem u9411 : Upper (D 6) (R 6) [6,33,72,18,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9411
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9412 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 26 400 36 97 225 353), lower := (rows 7 35 76 26 400 36 64 128 256), losses := [] }

theorem u9412 : Upper (D 6) (R 6) [6,33,72,18,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9412
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9413 : Route 9 := (fun mask => (mask,id))

def c9413 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9413 : Upper (D 6) (R 6) [6,33,72,18,384,64] 13 := by
  apply FastRouting.sound _ _ [6,33,72,18,384,64] 13 (by decide) (choices 1) [1,4,32] r9413 c9413
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1009
  · exact u1010
  · exact u1011

def b9414 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 28 176 33 322 450 322), lower := (rows 7 35 76 28 176 33 64 128 256), losses := [] }

theorem u9414 : Upper (D 6) (R 6) [6,33,72,20,160,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9414
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9415 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 28 176 34 321 449 321), lower := (rows 7 35 76 28 176 34 64 128 256), losses := [] }

theorem u9415 : Upper (D 6) (R 6) [6,33,72,20,160,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9415
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9416 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 498, targets := 4 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 28 176 96 323 387 259), lower := (rows 7 35 76 28 176 96 64 128 256), losses := [] }

theorem u9416 : Upper (D 6) (R 6) [6,33,72,20,160,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9416
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9417 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 498, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 28 176 288 67 195 323), lower := (rows 7 35 76 28 176 288 64 128 256), losses := [] }

theorem u9417 : Upper (D 6) (R 6) [6,33,72,20,160,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9417
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9418 : PairBound 9 := { available := 98, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 28 400 33 98 226 354), lower := (rows 7 35 76 28 400 33 64 128 256), losses := [] }

theorem u9418 : Upper (D 6) (R 6) [6,33,72,20,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9418
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9419 : PairBound 9 := { available := 97, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 28 400 34 97 225 353), lower := (rows 7 35 76 28 400 34 64 128 256), losses := [] }

theorem u9419 : Upper (D 6) (R 6) [6,33,72,20,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9419
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9419
end Delivery.IrregularNine14.P06
