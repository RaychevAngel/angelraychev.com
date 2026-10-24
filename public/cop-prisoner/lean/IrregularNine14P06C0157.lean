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

def b9420 : PairBound 9 := { available := 35, camps := [{ cop := 0, region := 498, targets := 4 },{ cop := 1, region := 400, targets := 64 }], pairs := [(1,2),(4,2),(4,6)], upper := (rows 7 35 76 28 400 96 99 163 291), lower := (rows 7 35 76 28 400 96 64 128 256), losses := [] }

theorem u9420 : Upper (D 6) (R 6) [6,33,72,20,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9420
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9421 : PairBound 9 := { available := 324, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 56 146 33 324 452 324), lower := (rows 7 35 76 56 146 33 64 128 256), losses := [] }

theorem u9421 : Upper (D 6) (R 6) [6,33,72,48,130,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9421
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9422 : PairBound 9 := { available := 321, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 56 146 36 321 449 321), lower := (rows 7 35 76 56 146 36 64 128 256), losses := [] }

theorem u9422 : Upper (D 6) (R 6) [6,33,72,48,130,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9422
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9423 : PairBound 9 := { available := 261, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(3,1),(4,5),(4,6)], upper := (rows 7 35 76 56 146 96 325 389 261), lower := (rows 7 35 76 56 146 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 103 65 129 257), good := (rows 485 481 108 56 184 96 96 128 256) }] }

theorem u9423 : Upper (D 6) (R 6) [6,33,72,48,130,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9423
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9424 : PairBound 9 := { available := 69, camps := [{ cop := 0, region := 208, targets := 32 }], pairs := [(3,1),(4,5)], upper := (rows 7 35 76 56 146 288 69 197 325), lower := (rows 7 35 76 56 146 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 4 24 16 291 65 129 257), good := (rows 485 481 76 56 184 288 64 128 288) }] }

theorem u9424 : Upper (D 6) (R 6) [6,33,72,48,130,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9424
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9425 : PairBound 9 := { available := 322, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 56 148 33 322 450 322), lower := (rows 7 35 76 56 148 33 64 128 256), losses := [] }

theorem u9425 : Upper (D 6) (R 6) [6,33,72,48,132,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9425
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9426 : PairBound 9 := { available := 321, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 56 148 34 321 449 321), lower := (rows 7 35 76 56 148 34 64 128 256), losses := [] }

theorem u9426 : Upper (D 6) (R 6) [6,33,72,48,132,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9426
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9427 : PairBound 9 := { available := 259, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 56 148 96 323 387 259), lower := (rows 7 35 76 56 148 96 64 128 256), losses := [] }

theorem u9427 : Upper (D 6) (R 6) [6,33,72,48,132,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9427
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9428 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 354, targets := 4 },{ cop := 0, region := 208, targets := 32 }], pairs := [(1,2),(4,5)], upper := (rows 7 35 76 56 148 288 67 195 323), lower := (rows 7 35 76 56 148 288 64 128 256), losses := [] }

theorem u9428 : Upper (D 6) (R 6) [6,33,72,48,132,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9428
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9429 : PairBound 9 := { available := 70, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 56 400 33 70 198 326), lower := (rows 7 35 76 56 400 33 64 128 256), losses := [] }

theorem u9429 : Upper (D 6) (R 6) [6,33,72,48,384,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9429
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9430 : PairBound 9 := { available := 69, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 56 400 34 69 197 325), lower := (rows 7 35 76 56 400 34 64 128 256), losses := [] }

theorem u9430 : Upper (D 6) (R 6) [6,33,72,48,384,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9430
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9431 : PairBound 9 := { available := 67, camps := [{ cop := 0, region := 464, targets := 36 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(4,2),(4,5)], upper := (rows 7 35 76 56 400 36 67 195 323), lower := (rows 7 35 76 56 400 36 64 128 256), losses := [] }

theorem u9431 : Upper (D 6) (R 6) [6,33,72,48,384,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9431
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9432 : PairBound 9 := { available := 7, camps := [{ cop := 0, region := 400, targets := 32 },{ cop := 0, region := 400, targets := 64 }], pairs := [(1,2),(4,5),(4,6)], upper := (rows 7 35 76 56 400 96 71 135 263), lower := (rows 7 35 76 56 400 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 56 400 96 96 128 256) }] }

theorem u9432 : Upper (D 6) (R 6) [6,33,72,48,384,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9432
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9433 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 137 82 36 368 432 304), lower := (rows 7 35 76 137 82 36 64 128 256), losses := [] }

theorem u9433 : Upper (D 6) (R 6) [6,33,72,129,66,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9433
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9434 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 82 48 356 420 292), lower := (rows 7 35 76 137 82 48 64 128 256), losses := [] }

theorem u9434 : Upper (D 6) (R 6) [6,33,72,129,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9434
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9435 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 76 137 82 288 116 180 308), lower := (rows 7 35 76 137 82 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 303 73 137 265), good := (rows 502 498 492 508 114 288 64 128 288) }] }

theorem u9435 : Upper (D 6) (R 6) [6,33,72,129,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9435
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9436 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 137 112 34 340 404 276), lower := (rows 7 35 76 137 112 34 64 128 256), losses := [] }

theorem u9436 : Upper (D 6) (R 6) [6,33,72,129,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9436
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9437 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 76 137 112 36 338 402 274), lower := (rows 7 35 76 137 112 36 64 128 256), losses := [] }

theorem u9437 : Upper (D 6) (R 6) [6,33,72,129,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9437
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9438 : PairBound 9 := { available := 262, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 137 112 48 326 390 262), lower := (rows 7 35 76 137 112 48 64 128 256), losses := [] }

theorem u9438 : Upper (D 6) (R 6) [6,33,72,129,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9438
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9439 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 76 137 112 288 86 150 278), lower := (rows 7 35 76 137 112 288 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 31 299 65 129 257), good := (rows 502 498 124 508 112 288 64 128 288) }] }

theorem u9439 : Upper (D 6) (R 6) [6,33,72,129,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9439
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9440 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 137 274 36 112 240 368), lower := (rows 7 35 76 137 274 36 64 128 256), losses := [] }

theorem u9440 : Upper (D 6) (R 6) [6,33,72,129,258,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9440
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9441 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 2 }], pairs := [(2,1),(3,1)], upper := (rows 7 35 76 137 274 48 100 228 356), lower := (rows 7 35 76 137 274 48 64 128 256), losses := [] }

theorem u9441 : Upper (D 6) (R 6) [6,33,72,129,258,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9441
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9442 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 76 137 274 96 116 180 308), lower := (rows 7 35 76 137 274 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 19 111 73 137 265), good := (rows 502 498 492 508 306 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 139 274 96 96 128 256) }] }

theorem u9442 : Upper (D 6) (R 6) [6,33,72,129,258,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9442
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9443 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 137 276 34 112 240 368), lower := (rows 7 35 76 137 276 34 64 128 256), losses := [] }

theorem u9443 : Upper (D 6) (R 6) [6,33,72,129,260,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9443
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9444 : PairBound 9 := { available := 98, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 137 276 48 98 226 354), lower := (rows 7 35 76 137 276 48 64 128 256), losses := [] }

theorem u9444 : Upper (D 6) (R 6) [6,33,72,129,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9444
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9445 : PairBound 9 := { available := 50, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 76 137 276 96 114 178 306), lower := (rows 7 35 76 137 276 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 25 111 67 131 259), good := (rows 502 498 124 508 308 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 139 304 96 96 128 256) }] }

theorem u9445 : Upper (D 6) (R 6) [6,33,72,129,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9445
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9446 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 137 304 34 84 212 340), lower := (rows 7 35 76 137 304 34 64 128 256), losses := [] }

theorem u9446 : Upper (D 6) (R 6) [6,33,72,129,288,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9446
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9447 : PairBound 9 := { available := 82, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 137 304 36 82 210 338), lower := (rows 7 35 76 137 304 36 64 128 256), losses := [] }

theorem u9447 : Upper (D 6) (R 6) [6,33,72,129,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9447
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9448 : PairBound 9 := { available := 70, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 137 304 48 70 198 326), lower := (rows 7 35 76 137 304 48 64 128 256), losses := [] }

theorem u9448 : Upper (D 6) (R 6) [6,33,72,129,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9448
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9449 : PairBound 9 := { available := 22, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(1,2),(2,0),(4,0)], upper := (rows 7 35 76 137 304 96 86 150 278), lower := (rows 7 35 76 137 304 96 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 111 65 129 257), good := (rows 502 498 124 508 304 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 139 304 96 96 128 256) }] }

theorem u9449 : Upper (D 6) (R 6) [6,33,72,129,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9449
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9450 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 137 336 34 116 180 308), lower := (rows 7 35 76 137 336 34 64 128 256), losses := [] }

theorem u9450 : Upper (D 6) (R 6) [6,33,72,129,320,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9450
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9451 : PairBound 9 := { available := 50, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 137 336 36 114 178 306), lower := (rows 7 35 76 137 336 36 64 128 256), losses := [] }

theorem u9451 : Upper (D 6) (R 6) [6,33,72,129,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9451
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9452 : PairBound 9 := { available := 38, camps := [{ cop := 0, region := 368, targets := 1 }], pairs := [(2,0),(4,0)], upper := (rows 7 35 76 137 336 48 102 166 294), lower := (rows 7 35 76 137 336 48 64 128 256), losses := [{ target := 0, region := (rows 0 2 12 8 27 63 65 129 257), good := (rows 502 498 124 508 368 48 64 128 256) }] }

theorem u9452 : Upper (D 6) (R 6) [6,33,72,129,320,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9452
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9453 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 138 81 36 368 432 304), lower := (rows 7 35 76 138 81 36 64 128 256), losses := [] }

theorem u9453 : Upper (D 6) (R 6) [6,33,72,130,65,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9453
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9454 : PairBound 9 := { available := 292, camps := [{ cop := 1, region := 460, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 81 48 356 420 292), lower := (rows 7 35 76 138 81 48 64 128 256), losses := [] }

theorem u9454 : Upper (D 6) (R 6) [6,33,72,130,65,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9454
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9455 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(2,1),(4,1)], upper := (rows 7 35 76 138 81 288 116 180 308), lower := (rows 7 35 76 138 81 288 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 319 73 137 265), good := (rows 501 497 492 508 497 288 64 128 288) }] }

theorem u9455 : Upper (D 6) (R 6) [6,33,72,130,65,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9455
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9456 : PairBound 9 := { available := 276, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 138 112 33 340 404 276), lower := (rows 7 35 76 138 112 33 64 128 256), losses := [] }

theorem u9456 : Upper (D 6) (R 6) [6,33,72,130,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9456
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9457 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 48, targets := 1 }], pairs := [(3,2),(4,0),(4,2)], upper := (rows 7 35 76 138 112 36 337 401 273), lower := (rows 7 35 76 138 112 36 64 128 256), losses := [] }

theorem u9457 : Upper (D 6) (R 6) [6,33,72,130,96,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9457
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9458 : PairBound 9 := { available := 261, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 138 112 48 325 389 261), lower := (rows 7 35 76 138 112 48 64 128 256), losses := [] }

theorem u9458 : Upper (D 6) (R 6) [6,33,72,130,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9458
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9459 : Route 9 := (fun mask => (mask,id))

def c9459 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 32 => 5 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9459 : Upper (D 6) (R 6) [6,33,72,130,96,256] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,96,256] 13 (by decide) (choices 1) [1,4,16] r9459 c9459
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1012
  · exact u1013
  · exact u1014

def b9460 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 138 273 36 112 240 368), lower := (rows 7 35 76 138 273 36 64 128 256), losses := [] }

theorem u9460 : Upper (D 6) (R 6) [6,33,72,130,257,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9460
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9461 : PairBound 9 := { available := 100, camps := [{ cop := 1, region := 204, targets := 1 }], pairs := [(2,0),(3,0)], upper := (rows 7 35 76 138 273 48 100 228 356), lower := (rows 7 35 76 138 273 48 64 128 256), losses := [] }

theorem u9461 : Upper (D 6) (R 6) [6,33,72,130,257,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9461
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9462 : PairBound 9 := { available := 52, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 76 138 273 96 116 180 308), lower := (rows 7 35 76 138 273 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 19 127 73 137 265), good := (rows 501 497 492 508 497 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 138 275 96 96 128 256) }] }

theorem u9462 : Upper (D 6) (R 6) [6,33,72,130,257,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9462
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9463 : PairBound 9 := { available := 112, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 138 276 33 112 240 368), lower := (rows 7 35 76 138 276 33 64 128 256), losses := [] }

theorem u9463 : Upper (D 6) (R 6) [6,33,72,130,260,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9463
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9464 : PairBound 9 := { available := 97, camps := [{ cop := 4, region := 35, targets := 64 }], pairs := [(0,6),(1,6)], upper := (rows 7 35 76 138 276 48 97 225 353), lower := (rows 7 35 76 138 276 48 64 128 256), losses := [] }

theorem u9464 : Upper (D 6) (R 6) [6,33,72,130,260,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9464
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9465 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(1,2),(2,1),(4,1)], upper := (rows 7 35 76 138 276 96 113 177 305), lower := (rows 7 35 76 138 276 96 64 128 256), losses := [{ target := 1, region := (rows 1 0 12 8 25 111 67 131 259), good := (rows 501 497 124 508 308 96 96 128 256) },{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 138 304 96 96 128 256) }] }

theorem u9465 : Upper (D 6) (R 6) [6,33,72,130,260,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9465
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9466 : PairBound 9 := { available := 84, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 138 304 33 84 212 340), lower := (rows 7 35 76 138 304 33 64 128 256), losses := [] }

theorem u9466 : Upper (D 6) (R 6) [6,33,72,130,288,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9466
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9467 : PairBound 9 := { available := 81, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 138 304 36 81 209 337), lower := (rows 7 35 76 138 304 36 64 128 256), losses := [] }

theorem u9467 : Upper (D 6) (R 6) [6,33,72,130,288,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9467
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9468 : PairBound 9 := { available := 69, camps := [{ cop := 8, region := 48, targets := 3 }], pairs := [(4,0),(4,1)], upper := (rows 7 35 76 138 304 48 69 197 325), lower := (rows 7 35 76 138 304 48 64 128 256), losses := [] }

theorem u9468 : Upper (D 6) (R 6) [6,33,72,130,288,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9468
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9469 : PairBound 9 := { available := 21, camps := [{ cop := 0, region := 368, targets := 2 }], pairs := [(1,2),(3,6),(4,1)], upper := (rows 7 35 76 138 304 96 85 149 277), lower := (rows 7 35 76 138 304 96 64 128 256), losses := [{ target := 2, region := (rows 1 3 0 8 16 100 64 128 256), good := (rows 35 35 104 138 304 96 96 128 256) },{ target := 6, region := (rows 1 2 4 11 18 32 0 129 257), good := (rows 415 443 12 154 304 32 0 128 256) }] }

theorem u9469 : Upper (D 6) (R 6) [6,33,72,130,288,64] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9469
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9470 : PairBound 9 := { available := 52, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 138 336 33 116 180 308), lower := (rows 7 35 76 138 336 33 64 128 256), losses := [] }

theorem u9470 : Upper (D 6) (R 6) [6,33,72,130,320,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9470
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9471 : PairBound 9 := { available := 49, camps := [{ cop := 1, region := 472, targets := 4 },{ cop := 2, region := 35, targets := 64 }], pairs := [(0,6),(3,2),(4,2)], upper := (rows 7 35 76 138 336 36 113 177 305), lower := (rows 7 35 76 138 336 36 64 128 256), losses := [] }

theorem u9471 : Upper (D 6) (R 6) [6,33,72,130,320,4] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9471
    (constants 6).1 (constants 6).2 (by decide +kernel)

def r9472 : Route 9 := (fun mask => (mask,id))

def c9472 : Nat → Fin 9 := (fun mask => match mask with | 2 => 1 | 8 => 3 | 16 => 4 | 128 => 7 | 256 => 8 | _ => 0)

theorem u9472 : Upper (D 6) (R 6) [6,33,72,130,320,16] 13 := by
  apply FastRouting.sound _ _ [6,33,72,130,320,16] 13 (by decide) (choices 1) [1,4,32] r9472 c9472
    (by exact cover_one)
    (by decide +kernel)
  intro mask member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl
  · exact u1015
  · exact u1016
  · exact u1017

def b9473 : PairBound 9 := { available := 304, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 140 82 33 368 432 304), lower := (rows 7 35 76 140 82 33 64 128 256), losses := [] }

theorem u9473 : Upper (D 6) (R 6) [6,33,72,132,66,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9473
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9474 : PairBound 9 := { available := 289, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 82 48 353 417 289), lower := (rows 7 35 76 140 82 48 64 128 256), losses := [] }

theorem u9474 : Upper (D 6) (R 6) [6,33,72,132,66,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9474
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9475 : PairBound 9 := { available := 49, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 82 288 113 177 305), lower := (rows 7 35 76 140 82 288 64 128 256), losses := [] }

theorem u9475 : Upper (D 6) (R 6) [6,33,72,132,66,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9475
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9476 : PairBound 9 := { available := 274, camps := [{ cop := 1, region := 476, targets := 1 }], pairs := [(2,0),(3,0),(4,0)], upper := (rows 7 35 76 140 112 33 338 402 274), lower := (rows 7 35 76 140 112 33 64 128 256), losses := [] }

theorem u9476 : Upper (D 6) (R 6) [6,33,72,132,96,1] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9476
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9477 : PairBound 9 := { available := 273, camps := [{ cop := 1, region := 476, targets := 2 }], pairs := [(2,1),(3,1),(4,1)], upper := (rows 7 35 76 140 112 34 337 401 273), lower := (rows 7 35 76 140 112 34 64 128 256), losses := [] }

theorem u9477 : Upper (D 6) (R 6) [6,33,72,132,96,2] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9477
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9478 : PairBound 9 := { available := 259, camps := [{ cop := 1, region := 461, targets := 32 }], pairs := [(0,5),(2,5)], upper := (rows 7 35 76 140 112 48 323 387 259), lower := (rows 7 35 76 140 112 48 64 128 256), losses := [] }

theorem u9478 : Upper (D 6) (R 6) [6,33,72,132,96,16] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9478
    (constants 6).1 (constants 6).2 (by decide +kernel)

def b9479 : PairBound 9 := { available := 19, camps := [{ cop := 0, region := 370, targets := 4 }], pairs := [(1,2),(4,2)], upper := (rows 7 35 76 140 112 288 83 147 275), lower := (rows 7 35 76 140 112 288 64 128 256), losses := [] }

theorem u9479 : Upper (D 6) (R 6) [6,33,72,132,96,256] 13 :=
  PairNine.sound _ _ _ _ (leftConstant 6) 14 b9479
    (constants 6).1 (constants 6).2 (by decide +kernel)

#print axioms u9479
end Delivery.IrregularNine14.P06
