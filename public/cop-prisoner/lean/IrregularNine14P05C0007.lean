import RowPrefixPairLoss
import IrregularNine14Constants
import RowPrefixCampingNine
import RowPrefixPermutationNine
import RowPrefixFastRouting

namespace Delivery.IrregularNine14.P05
open RowPrefix
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def b420 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 84 138 280 40 65 164 292), lower := (rows 7 35 84 138 280 40 65 128 256), losses := [] }

theorem u420 : Upper (D 5) (R 5) [6,33,80,130,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b420
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b421 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 138 280 40 68 161 289), lower := (rows 7 35 84 138 280 40 68 128 256), losses := [] }

theorem u421 : Upper (D 5) (R 5) [6,33,80,130,264,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b421
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b422 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 84 138 280 40 96 133 261), lower := (rows 7 35 84 138 280 40 96 128 256), losses := [] }

theorem u422 : Upper (D 5) (R 5) [6,33,80,130,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b422
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b423 : PairBound 9 := { available := 12, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 84 138 304 40 65 140 268), lower := (rows 7 35 84 138 304 40 65 128 256), losses := [] }

theorem u423 : Upper (D 5) (R 5) [6,33,80,130,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b423
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b424 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 170, targets := 4 }], pairs := [(1,2),(3,2)], upper := (rows 7 35 84 138 304 40 68 137 265), lower := (rows 7 35 84 138 304 40 68 128 256), losses := [] }

theorem u424 : Upper (D 5) (R 5) [6,33,80,130,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b424
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b425 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(2,0),(3,5)], upper := (rows 7 35 84 138 304 40 72 133 261), lower := (rows 7 35 84 138 304 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 20 8 16 104 104 128 256), good := (rows 6 98 116 234 372 104 104 128 256) }] }

theorem u425 : Upper (D 5) (R 5) [6,33,80,130,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b425
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b426 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 440, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 84 140 280 40 65 162 290), lower := (rows 7 35 84 140 280 40 65 128 256), losses := [] }

theorem u426 : Upper (D 5) (R 5) [6,33,80,132,264,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b426
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b427 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 440, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 84 140 280 40 66 161 289), lower := (rows 7 35 84 140 280 40 66 128 256), losses := [] }

theorem u427 : Upper (D 5) (R 5) [6,33,80,132,264,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b427
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b428 : PairBound 9 := { available := 3, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 84 140 280 40 96 131 259), lower := (rows 7 35 84 140 280 40 96 128 256), losses := [] }

theorem u428 : Upper (D 5) (R 5) [6,33,80,132,264,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b428
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b429 : PairBound 9 := { available := 10, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 84 140 304 40 65 138 266), lower := (rows 7 35 84 140 304 40 65 128 256), losses := [] }

theorem u429 : Upper (D 5) (R 5) [6,33,80,132,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b429
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b430 : PairBound 9 := { available := 9, camps := [{ cop := 4, region := 71, targets := 8 }], pairs := [(0,3),(1,3)], upper := (rows 7 35 84 140 304 40 66 137 265), lower := (rows 7 35 84 140 304 40 66 128 256), losses := [] }

theorem u430 : Upper (D 5) (R 5) [6,33,80,132,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b430
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b431 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 84 140 304 40 72 131 259), lower := (rows 7 35 84 140 304 40 72 128 256), losses := [] }

theorem u431 : Upper (D 5) (R 5) [6,33,80,132,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b431
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b432 : PairBound 9 := { available := 36, camps := [{ cop := 4, region := 69, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 35 84 392 26 40 65 164 292), lower := (rows 7 35 84 392 26 40 65 128 256), losses := [] }

theorem u432 : Upper (D 5) (R 5) [6,33,80,384,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b432
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b433 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 69, targets := 40 }], pairs := [(0,3),(0,5)], upper := (rows 7 35 84 392 26 40 68 161 289), lower := (rows 7 35 84 392 26 40 68 128 256), losses := [] }

theorem u433 : Upper (D 5) (R 5) [6,33,80,384,10,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b433
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b434 : PairBound 9 := { available := 5, camps := [{ cop := 0, region := 408, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 84 392 26 40 96 133 261), lower := (rows 7 35 84 392 26 40 96 128 256), losses := [] }

theorem u434 : Upper (D 5) (R 5) [6,33,80,384,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b434
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b435 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 25 276 40 66 168 296), lower := (rows 7 35 196 25 276 40 66 128 256), losses := [] }

theorem u435 : Upper (D 5) (R 5) [6,33,192,17,260,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b435
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b436 : PairBound 9 := { available := 34, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 196 25 276 40 72 162 290), lower := (rows 7 35 196 25 276 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 6 8 19 104 104 130 258), good := (rows 406 502 228 120 276 104 104 128 256) }] }

theorem u436 : Upper (D 5) (R 5) [6,33,192,17,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b436
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b437 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 25 276 40 96 138 266), lower := (rows 7 35 196 25 276 40 96 128 256), losses := [] }

theorem u437 : Upper (D 5) (R 5) [6,33,192,17,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b437
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b438 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 25 304 40 66 140 268), lower := (rows 7 35 196 25 304 40 66 128 256), losses := [] }

theorem u438 : Upper (D 5) (R 5) [6,33,192,17,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b438
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b439 : PairBound 9 := { available := 10, camps := [{ cop := 7, region := 68, targets := 3 }], pairs := [(2,0),(2,1)], upper := (rows 7 35 196 25 304 40 68 138 266), lower := (rows 7 35 196 25 304 40 68 128 256), losses := [] }

theorem u439 : Upper (D 5) (R 5) [6,33,192,17,288,8,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b439
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b440 : PairBound 9 := { available := 6, camps := [{ cop := 3, region := 34, targets := 4 }], pairs := [(1,2),(2,0)], upper := (rows 7 35 196 25 304 40 72 134 262), lower := (rows 7 35 196 25 304 40 72 128 256), losses := [{ target := 0, region := (rows 0 2 14 8 26 104 104 131 259), good := (rows 406 502 228 508 368 124 124 128 256) }] }

theorem u440 : Upper (D 5) (R 5) [6,33,192,17,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b440
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b441 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 26 276 40 65 168 296), lower := (rows 7 35 196 26 276 40 65 128 256), losses := [] }

theorem u441 : Upper (D 5) (R 5) [6,33,192,18,260,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b441
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b442 : PairBound 9 := { available := 33, camps := [], pairs := [(2,1),(4,1)], upper := (rows 7 35 196 26 276 40 72 161 289), lower := (rows 7 35 196 26 276 40 72 128 256), losses := [{ target := 1, region := (rows 1 0 14 8 27 104 104 130 258), good := (rows 405 501 228 508 276 124 124 128 256) }] }

theorem u442 : Upper (D 5) (R 5) [6,33,192,18,260,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b442
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b443 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 26 276 40 96 137 265), lower := (rows 7 35 196 26 276 40 96 128 256), losses := [] }

theorem u443 : Upper (D 5) (R 5) [6,33,192,18,260,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b443
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b444 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 28 273 40 66 168 296), lower := (rows 7 35 196 28 273 40 66 128 256), losses := [] }

theorem u444 : Upper (D 5) (R 5) [6,33,192,20,257,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b444
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b445 : PairBound 9 := { available := 34, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 28 273 40 72 162 290), lower := (rows 7 35 196 28 273 40 72 128 256), losses := [] }

theorem u445 : Upper (D 5) (R 5) [6,33,192,20,257,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b445
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b446 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 28 273 40 96 138 266), lower := (rows 7 35 196 28 273 40 96 128 256), losses := [] }

theorem u446 : Upper (D 5) (R 5) [6,33,192,20,257,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b446
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b447 : PairBound 9 := { available := 40, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 28 274 40 65 168 296), lower := (rows 7 35 196 28 274 40 65 128 256), losses := [] }

theorem u447 : Upper (D 5) (R 5) [6,33,192,20,258,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b447
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b448 : PairBound 9 := { available := 33, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 28 274 40 72 161 289), lower := (rows 7 35 196 28 274 40 72 128 256), losses := [] }

theorem u448 : Upper (D 5) (R 5) [6,33,192,20,258,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b448
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b449 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 28 274 40 96 137 265), lower := (rows 7 35 196 28 274 40 96 128 256), losses := [] }

theorem u449 : Upper (D 5) (R 5) [6,33,192,20,258,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b449
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b450 : PairBound 9 := { available := 10, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 28 304 40 65 138 266), lower := (rows 7 35 196 28 304 40 65 128 256), losses := [] }

theorem u450 : Upper (D 5) (R 5) [6,33,192,20,288,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b450
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b451 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 28 304 40 66 137 265), lower := (rows 7 35 196 28 304 40 66 128 256), losses := [] }

theorem u451 : Upper (D 5) (R 5) [6,33,192,20,288,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b451
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b452 : PairBound 9 := { available := 3, camps := [{ cop := 1, region := 272, targets := 12 }], pairs := [(4,2),(4,3)], upper := (rows 7 35 196 28 304 40 72 131 259), lower := (rows 7 35 196 28 304 40 72 128 256), losses := [] }

theorem u452 : Upper (D 5) (R 5) [6,33,192,20,288,8,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b452
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b453 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 265 28 40 66 176 304), lower := (rows 7 35 196 265 28 40 66 128 256), losses := [] }

theorem u453 : Upper (D 5) (R 5) [6,33,192,257,12,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b453
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b454 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 298, targets := 4 }], pairs := [(1,2)], upper := (rows 7 35 196 265 28 40 80 162 290), lower := (rows 7 35 196 265 28 40 80 128 256), losses := [] }

theorem u454 : Upper (D 5) (R 5) [6,33,192,257,12,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b454
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b455 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 265 28 40 96 146 274), lower := (rows 7 35 196 265 28 40 96 128 256), losses := [] }

theorem u455 : Upper (D 5) (R 5) [6,33,192,257,12,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b455
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b456 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 312, targets := 2 }], pairs := [(3,1),(4,1)], upper := (rows 7 35 196 268 25 40 66 176 304), lower := (rows 7 35 196 268 25 40 66 128 256), losses := [] }

theorem u456 : Upper (D 5) (R 5) [6,33,192,260,9,8,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b456
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b457 : PairBound 9 := { available := 34, camps := [{ cop := 0, region := 296, targets := 1 }], pairs := [(3,0)], upper := (rows 7 35 196 268 25 40 80 162 290), lower := (rows 7 35 196 268 25 40 80 128 256), losses := [] }

theorem u457 : Upper (D 5) (R 5) [6,33,192,260,9,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b457
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b458 : PairBound 9 := { available := 18, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 268 25 40 96 146 274), lower := (rows 7 35 196 268 25 40 96 128 256), losses := [] }

theorem u458 : Upper (D 5) (R 5) [6,33,192,260,9,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b458
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b459 : PairBound 9 := { available := 48, camps := [{ cop := 0, region := 312, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 35 196 268 26 40 65 176 304), lower := (rows 7 35 196 268 26 40 65 128 256), losses := [] }

theorem u459 : Upper (D 5) (R 5) [6,33,192,260,10,8,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b459
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b460 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 296, targets := 2 }], pairs := [(3,1)], upper := (rows 7 35 196 268 26 40 80 161 289), lower := (rows 7 35 196 268 26 40 80 128 256), losses := [] }

theorem u460 : Upper (D 5) (R 5) [6,33,192,260,10,8,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b460
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b461 : PairBound 9 := { available := 17, camps := [{ cop := 0, region := 280, targets := 32 }], pairs := [(3,5),(4,5)], upper := (rows 7 35 196 268 26 40 96 145 273), lower := (rows 7 35 196 268 26 40 96 128 256), losses := [] }

theorem u461 : Upper (D 5) (R 5) [6,33,192,260,10,8,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b461
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b462 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 26 145 288 68 168 296), lower := (rows 7 42 69 26 145 288 68 128 256), losses := [] }

theorem u462 : Upper (D 5) (R 5) [6,40,65,18,129,256,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b462
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b463 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 432, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 26 145 288 72 164 292), lower := (rows 7 42 69 26 145 288 72 128 256), losses := [] }

theorem u463 : Upper (D 5) (R 5) [6,40,65,18,129,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b463
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b464 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 26 145 288 96 140 268), lower := (rows 7 42 69 26 145 288 96 128 256), losses := [] }

theorem u464 : Upper (D 5) (R 5) [6,40,65,18,129,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b464
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b465 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 26 148 288 65 168 296), lower := (rows 7 42 69 26 148 288 65 128 256), losses := [] }

theorem u465 : Upper (D 5) (R 5) [6,40,65,18,132,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b465
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b466 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 2 }], pairs := [(4,1)], upper := (rows 7 42 69 26 148 288 72 161 289), lower := (rows 7 42 69 26 148 288 72 128 256), losses := [] }

theorem u466 : Upper (D 5) (R 5) [6,40,65,18,132,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b466
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b467 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 26 148 288 96 137 265), lower := (rows 7 42 69 26 148 288 96 128 256), losses := [] }

theorem u467 : Upper (D 5) (R 5) [6,40,65,18,132,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b467
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b468 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 400 33 68 168 296), lower := (rows 7 42 69 26 400 33 68 128 256), losses := [] }

theorem u468 : Upper (D 5) (R 5) [6,40,65,18,384,1,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b468
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b469 : PairBound 9 := { available := 36, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 69 26 400 33 72 164 292), lower := (rows 7 42 69 26 400 33 72 128 256), losses := [] }

theorem u469 : Upper (D 5) (R 5) [6,40,65,18,384,1,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b469
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b470 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 408, targets := 1 }], pairs := [(3,0),(4,0)], upper := (rows 7 42 69 26 400 33 96 140 268), lower := (rows 7 42 69 26 400 33 96 128 256), losses := [] }

theorem u470 : Upper (D 5) (R 5) [6,40,65,18,384,1,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b470
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b471 : PairBound 9 := { available := 40, camps := [{ cop := 5, region := 410, targets := 5 }], pairs := [(1,0),(1,2)], upper := (rows 7 42 69 26 400 36 65 168 296), lower := (rows 7 42 69 26 400 36 65 128 256), losses := [] }

theorem u471 : Upper (D 5) (R 5) [6,40,65,18,384,4,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b471
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b472 : PairBound 9 := { available := 33, camps := [{ cop := 0, region := 432, targets := 10 }], pairs := [(4,1),(4,3)], upper := (rows 7 42 69 26 400 36 72 161 289), lower := (rows 7 42 69 26 400 36 72 128 256), losses := [] }

theorem u472 : Upper (D 5) (R 5) [6,40,65,18,384,4,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b472
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b473 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 408, targets := 36 }], pairs := [(3,2),(3,5)], upper := (rows 7 42 69 26 400 36 96 137 265), lower := (rows 7 42 69 26 400 36 96 128 256), losses := [] }

theorem u473 : Upper (D 5) (R 5) [6,40,65,18,384,4,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b473
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b474 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 28 146 288 65 168 296), lower := (rows 7 42 69 28 146 288 65 128 256), losses := [] }

theorem u474 : Upper (D 5) (R 5) [6,40,65,20,130,256,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b474
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b475 : PairBound 9 := { available := 33, camps := [{ cop := 4, region := 77, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 69 28 146 288 72 161 289), lower := (rows 7 42 69 28 146 288 72 128 256), losses := [] }

theorem u475 : Upper (D 5) (R 5) [6,40,65,20,130,256,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b475
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b476 : PairBound 9 := { available := 9, camps := [{ cop := 0, region := 152, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 28 146 288 96 137 265), lower := (rows 7 42 69 28 146 288 96 128 256), losses := [] }

theorem u476 : Upper (D 5) (R 5) [6,40,65,20,130,256,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b476
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b477 : PairBound 9 := { available := 40, camps := [{ cop := 1, region := 69, targets := 8 }], pairs := [(0,3)], upper := (rows 7 42 69 137 274 48 68 168 296), lower := (rows 7 42 69 137 274 48 68 128 256), losses := [] }

theorem u477 : Upper (D 5) (R 5) [6,40,65,129,258,16,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b477
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b478 : PairBound 9 := { available := 36, camps := [{ cop := 1, region := 69, targets := 32 }], pairs := [(0,5)], upper := (rows 7 42 69 137 274 48 72 164 292), lower := (rows 7 42 69 137 274 48 72 128 256), losses := [] }

theorem u478 : Upper (D 5) (R 5) [6,40,65,129,258,16,8] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b478
    (constants 5).1 (constants 5).2 (by decide +kernel)

def b479 : PairBound 9 := { available := 12, camps := [{ cop := 0, region := 136, targets := 32 }], pairs := [(3,5)], upper := (rows 7 42 69 137 274 48 96 140 268), lower := (rows 7 42 69 137 274 48 96 128 256), losses := [] }

theorem u479 : Upper (D 5) (R 5) [6,40,65,129,258,16,32] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 5) 14 b479
    (constants 5).1 (constants 5).2 (by decide +kernel)

#print axioms u479
end Delivery.IrregularNine14.P05
